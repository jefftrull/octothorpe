/**
 *  Sample program demonstrating extracting position information from C++ code
 *
 *   Copyright (C) 2021 Jeff Trull
 *
 *   Distributed under the Boost Software License, Version 1.0. (See accompanying
 *   file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
 *
 */

#include <iostream>
#include <fstream>
#include <iomanip>
// this code is intended to only require C++11; if you can, use the C++17 versions instead:
#include <boost/optional.hpp>
#include <boost/variant.hpp>

#include <boost/spirit/include/lex_plain_token.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix.hpp>
#include <boost/spirit/include/support_istream_iterator.hpp>
#include <boost/fusion/include/define_struct.hpp>

#ifdef BOOST_SPIRIT_DEBUG
#include <boost/optional/optional_io.hpp>
#include <boost/fusion/include/io.hpp>
#endif

#include "qi_token.hpp"

#include <boost/wave/token_ids.hpp>


template<typename Iterator>
struct skipper : boost::spirit::qi::grammar<Iterator>
{
    skipper() : skipper::base_type(skipped)
    {
        using namespace boost::spirit::qi;
        using namespace boost::wave;

        skipped = +(token(T_CCOMMENT) | token(T_CPPCOMMENT) | token(T_SPACE) | token(T_NEWLINE));
    }
private:
    boost::spirit::qi::rule<Iterator> skipped;
};

// forward declaration of statement types, so we can use them in recursive structures
template<typename Position>
struct empty_stmt_t;

template<typename Position>
struct expr_stmt_t;

template<typename Position>
struct if_stmt_t;

template<typename Position>
struct else_t;                 // the else clause of an if

template<typename Position>
struct while_stmt_t;

template<typename Position>
struct for_stmt_t;

// a type for "any statement" we can refer to in defining child statements
template<typename Position>
using simple_stmt_t = boost::variant<empty_stmt_t<Position>,
                                     if_stmt_t<Position>,
                                     while_stmt_t<Position>,
                                     for_stmt_t<Position>,
                                     expr_stmt_t<Position>>;

// handle compound (braced list) statements
template<typename Position>
struct compound_stmt_t;

template<typename Position>
using stmt_t = boost::variant<simple_stmt_t<Position>,
                              compound_stmt_t<Position>>;

BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    compound_stmt_t,
    (Position, initial_brace)
    (std::vector<stmt_t<Position>>, statements)
    (Position, final_brace)
)

BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    empty_stmt_t,
    (Position, semi)                                    // location of the semicolon
)

BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    expr_stmt_t,
    (Position, start)                                   // location of the first token
)

// attribute for if statements
BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    if_stmt_t,
    (Position, kwd)                                     // location of "if"
    (boost::recursive_wrapper<stmt_t<Position>>, stmt)  // location of true branch statement
    (boost::optional<else_t<Position>>, else_clause)    // else clause, if present
)

// attribute for else clause of if
BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    else_t,
    (Position, kwd)                                     // location of "else"
    (boost::recursive_wrapper<stmt_t<Position>>, stmt)  // location of statement
)

// attribute for while loops
BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    while_stmt_t,
    (Position, kwd)              // where we found "while"
    (boost::recursive_wrapper<stmt_t<Position>>, stmt)
)

// and for for loops
BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    for_stmt_t,
    (Position, kwd)              // where we found "for"
    (boost::recursive_wrapper<stmt_t<Position>>, stmt)
)

// functions
BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    func_t,
    (boost::optional<Position>, tmpl_expr)
    (Position, retval)
    (Position, name)
    (Position, lparen)
    (std::vector<Position>, params)
    (Position, rparen)
    (compound_stmt_t<Position>, body)
)

// namespaces: contain functions and other namespaces
template<typename Position> struct ns_t;
// create an alias to get around multiple comma issue in Fusion (due to macros)
template<typename Position>
using ns_var_t = boost::variant<func_t<Position>, ns_t<Position>>;

BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    ,
    ns_t,
    (Position, ns)
    (boost::optional<Position>, name)
    (Position, lbrace)
    (std::vector<ns_var_t<Position> >, contents)   // use our alias here
    (Position, rbrace)
)

#ifdef BOOST_SPIRIT_DEBUG
// supply printers for special types we use
using boost::fusion::operators::operator<<;

namespace boost {

template<typename Out, typename T>
Out& operator<<(Out& out, recursive_wrapper<T> const & val)
{
    out << val.get();
    return out;
}

}

namespace std {

template<typename Out, typename T>
Out& operator<<(Out& out, std::vector<T> const & val)
{
    out << "[";
    std::copy(std::begin(val), std::end(val), std::ostream_iterator<T>(cout, " "));
    out << "]";
    return out;
}

}

#endif // BOOST_SPIRIT_DEBUG

template<typename Iterator>
using result_t =
    std::vector<
        boost::variant<func_t<typename Iterator::position_type>,
                       ns_t<typename Iterator::position_type>>>;

template<typename Iterator>
struct cpp_indent : boost::spirit::qi::grammar<Iterator, skipper<Iterator>, result_t<Iterator>()>
{
    cpp_indent() : cpp_indent::base_type(cppfile)
    {
        using namespace boost::wave;
        using namespace boost::spirit;
        namespace phx = boost::phoenix;
        using qi::token;
        using qi::tokenid_mask;
        using qi::omit;

        qi::as<position_t> as_position;

        // operators are, in token mask terms, a subset of keywords
        kwd = tokenid_mask(KeywordTokenType) - tokenid_mask(OperatorTokenType) ;
        integral_type_kwd =
            token(T_BOOL) | token(T_INT) | token(T_CHAR) | token(T_LONG) |
            token(T_SHORT) | token(T_UNSIGNED) ;
        type_kwd =
            integral_type_kwd |
            token(T_FLOAT) | token(T_DOUBLE) | token(T_VOID) | token(T_AUTO) ;

        any_token = token(~0);            // treated internally as an "all mask"
        // did not use tokenid_mask here because it only exposes the tokenid, not the position!

        // thoughts
        // we need at the top level:
        // 1) rules for if, while, etc. that inherit the original indentation or calculate it
        //    based on the position of the keyword? Probably the latter.
        // 2) rules for braced-expression, unbraced, etc. or just "expression" that count
        //    parens/braces but are otherwise pretty generic
        // 3) crap out if we detect a tab
        // 4) if we don't know what we are looking at, skip current token and try again,
        //    possibly with adjustments if it's a brace or paren? Or maybe not.
        //    also skip any spaces/newlines after it.

        ident = token(T_IDENTIFIER) ;

        name =
            as_position[ident] >> *omit[ident | token(T_COLON_COLON) | token(T_TYPENAME) |
                           token(T_LESS) | token(T_GREATER) ] ;

        type_expr =
            ( type_kwd >> *omit[type_kwd] ) |
            name |
            ( token(T_DECLTYPE) >> omit[token(T_LEFTPAREN) >> expr >> token(T_RIGHTPAREN)] ) ;

        // an expression is a series of tokens not including semicolons or keywords,
        // with balanced parens/braces
        // its attribute is the position of the first token
        plain_expr_tok =
            (any_token - token(T_SEMICOLON) - kwd
             - token(T_LEFTPAREN) - token(T_LEFTBRACE)
             - token(T_RIGHTPAREN) - token(T_RIGHTBRACE)) ;

        expr =
            (as_position[token(T_LEFTPAREN)][_val = _1] >> expr >> token(T_RIGHTPAREN)) |
            (as_position[token(T_LEFTBRACE)][_val = _1] >> expr >> token(T_RIGHTBRACE)) |
            // function call - does not cover all possibilities, just plain identifier:
            (as_position[token(T_IDENTIFIER)][_val = _1] >>
             token(T_LEFTPAREN) >> -expr >> token(T_RIGHTPAREN)) |
            (plain_expr_tok[_val = _1] >> *plain_expr_tok) ;

        empty_stmt = as_position[token(T_SEMICOLON)] ;

        expr_stmt = expr >> omit[*expr] >> token(T_SEMICOLON) ;

        if_stmt = token(T_IF) >>
            omit[token(T_LEFTPAREN) >> expr >> token(T_RIGHTPAREN)] >>
            stmt >> -else_clause ;

        else_clause = token(T_ELSE) >> stmt ;

        while_stmt = token(T_WHILE) >>
            omit[ token(T_LEFTPAREN) >> expr >> token(T_RIGHTPAREN) ] >>
            stmt ;

        for_stmt = token(T_FOR) >>
            omit[token(T_LEFTPAREN) >>
                 -(-type_kwd >> expr) >> token(T_SEMICOLON) >>
                 -expr >> token(T_SEMICOLON) >>
                 -expr >> token(T_RIGHTPAREN)] >>
            stmt ;

        simple_stmt =
            empty_stmt | if_stmt | while_stmt | for_stmt | expr_stmt ;

        compound_stmt =
            token(T_LEFTBRACE) >> (*stmt) >> token(T_RIGHTBRACE);

        stmt = simple_stmt | compound_stmt ;

        func =
            -(token(T_TEMPLATE) >>
              omit[(token(T_LESS) >>
                    (((token(T_TYPENAME) | token(T_CLASS)) >> ident) |  // type
                     (integral_type_kwd >> ident))                      // integral constant
                    % token(T_COMMA)) >>
                   token(T_GREATER)]) >>
            as_position[type_expr] >> as_position[name] >>
            token(T_LEFTPAREN) >>
            -((as_position[type_expr] >> -omit[name]) % token(T_COMMA)) >>
            token(T_RIGHTPAREN) >>
            compound_stmt ;

        ns =
            token(T_NAMESPACE) >> -token(T_IDENTIFIER) >> token(T_LEFTBRACE) >>
            // within namespaces we expect functions and other namespaces
            *(func | ns |
              // but also, if we get confused we will skip a token and retry
              omit[any_token - token(T_RIGHTBRACE)]) >>
            token(T_RIGHTBRACE) ;

        cppfile = *(ns | func |                      // something we understood, or
                    omit[any_token - token(T_EOF)])  // a catchall to skip one token and retry
            >> omit[token(T_EOF)];                   // consume all input

        BOOST_SPIRIT_DEBUG_NODE(any_token);
        BOOST_SPIRIT_DEBUG_NODE(name);
        BOOST_SPIRIT_DEBUG_NODE(empty_stmt);
        BOOST_SPIRIT_DEBUG_NODE(type_expr);
        BOOST_SPIRIT_DEBUG_NODE(expr_stmt);
        BOOST_SPIRIT_DEBUG_NODE(if_stmt);
        BOOST_SPIRIT_DEBUG_NODE(else_clause);
        BOOST_SPIRIT_DEBUG_NODE(while_stmt);
        BOOST_SPIRIT_DEBUG_NODE(for_stmt);
        BOOST_SPIRIT_DEBUG_NODE(plain_expr_tok);
        BOOST_SPIRIT_DEBUG_NODE(expr);
        BOOST_SPIRIT_DEBUG_NODE(simple_stmt);
        BOOST_SPIRIT_DEBUG_NODE(compound_stmt);
        BOOST_SPIRIT_DEBUG_NODE(stmt);
        BOOST_SPIRIT_DEBUG_NODE(func);
        BOOST_SPIRIT_DEBUG_NODE(ns);
        BOOST_SPIRIT_DEBUG_NODE(cppfile);

    }
private:
    using position_t = typename Iterator::position_type;

    template<typename Attr>
    using rule = boost::spirit::qi::rule<Iterator, skipper<Iterator>, Attr()> ;
    template<typename Attr>
    using rule_no_skipper = boost::spirit::qi::rule<Iterator, Attr()> ;
    using rule_no_attr = boost::spirit::qi::rule<Iterator, skipper<Iterator>> ;

    rule<std::vector<boost::variant<func_t<position_t>, ns_t<position_t>>>> cppfile;

    rule<ns_t<position_t>> ns;

    rule<position_t> any_token;
    rule<position_t> plain_expr_tok;
    rule<position_t> expr;
    rule<position_t> type_kwd;
    rule<position_t> integral_type_kwd;
    rule<position_t> type_expr;
    rule_no_skipper<position_t> ident;
    rule_no_skipper<position_t> name;

    rule<simple_stmt_t<position_t>> simple_stmt;
    rule<compound_stmt_t<position_t>> compound_stmt;
    rule<stmt_t<position_t>> stmt;

    rule<empty_stmt_t<position_t>> empty_stmt;
    rule<if_stmt_t<position_t>> if_stmt;
    rule<else_t<position_t>> else_clause;
    rule<while_stmt_t<position_t>> while_stmt;
    rule<for_stmt_t<position_t>> for_stmt;
    rule<expr_stmt_t<position_t>> expr_stmt;

    rule<func_t<position_t>> func;

    rule_no_attr kwd;
};

struct stat_reporter : boost::static_visitor<void>
{
    stat_reporter()
        : num_ns(0), num_funcs(0), num_empty_stmts(0),
          num_if_stmts(0), num_while_stmts(0), num_for_stmts(0), num_expr_stmts(0)
    {}

    template<typename position_t>
    void operator()(empty_stmt_t<position_t> const &) { ++num_empty_stmts; }

    template<typename position_t>
    void operator()(expr_stmt_t<position_t> const &) { ++num_expr_stmts; }

    template<typename position_t>
    void operator()(if_stmt_t<position_t> const & s)
    {
        ++num_if_stmts;
        boost::apply_visitor(*this, s.stmt.get());
        if (s.else_clause)
            boost::apply_visitor(*this, (*s.else_clause).stmt.get());
    }

    template<typename position_t>
    void operator()(while_stmt_t<position_t> const & s)
    {
        ++num_while_stmts;
        boost::apply_visitor(*this, s.stmt.get());
    }

    template<typename position_t>
    void operator()(for_stmt_t<position_t> const & s)
    {
        ++num_for_stmts;
        boost::apply_visitor(*this, s.stmt.get());
    }

    template<typename position_t>
    void operator()(simple_stmt_t<position_t> const & s) { boost::apply_visitor(*this, s); }

    template<typename position_t>
    void operator()(compound_stmt_t<position_t> const & s)
    {
        for (auto const & s : s.statements)
            boost::apply_visitor(*this, s);
    }

    // function
    template<typename position_t>
    void operator()(func_t<position_t> const & f)
    {
        ++num_funcs;
        for (auto const & s : f.body.statements)
            boost::apply_visitor(*this, s);
    }

    // namespace - a collection of functions and namespaces
    template<typename position_t>
    void operator()(ns_t<position_t> const & ns)
    {
        ++num_ns;
        for (auto const & f_or_ns : ns.contents)
            boost::apply_visitor(*this, f_or_ns);
    }

    void report()
    {
        std::cout << num_ns << " namespaces and ";
        std::cout << num_funcs << " functions, containing ";
        std::cout << num_expr_stmts << " plain statements, ";
        std::cout << num_empty_stmts << " empty statements, ";
        std::cout << num_if_stmts << " if statements, ";
        std::cout << num_while_stmts << " while loops, and ";
        std::cout << num_for_stmts << " for loops.\n";
    }

private:
    std::size_t num_ns;
    std::size_t num_funcs;
    std::size_t num_empty_stmts;
    std::size_t num_if_stmts;
    std::size_t num_while_stmts;
    std::size_t num_for_stmts;
    std::size_t num_expr_stmts;
};



int main(int argc, char **argv) {
    using namespace std;
    using namespace boost::wave;

    if (argc != 2) {
        cerr << "usage: " << argv[0] << " path\n";
        return 1;
    }

    char const * fn = argv[1];

    ifstream cppfile(fn);
    if (!cppfile.is_open()) {
        cerr << "unable to open requested file " << fn << "\n";
        return 5;
    }
    cppfile.unsetf(ios::skipws);
    boost::spirit::istream_iterator fbeg(cppfile);

    // Give it a try
    using token_t = qi_token<>;
    using position_t = token_t::position_type;
    position_t pos(fn);

    // create Spirit V2-compatible lexer token iterators from character iterators
    using cpplexer_iterator_t = qi_lex_iterator<token_t>;
    cpplexer_iterator_t beg(fbeg, boost::spirit::istream_iterator(), pos,
                               language_support(support_cpp|support_cpp0x));
    cpplexer_iterator_t end;

    cpp_indent<decltype(beg)> fileparser;
    result_t<decltype(beg)> result;
    auto start = beg;
    bool pass = boost::spirit::qi::phrase_parse(beg, end, fileparser,
                                                skipper<decltype(beg)>(), result);
    if (pass) {
        if (beg == start) {
            cout << "no input consumed!\n";
            return 2;
        } else if (beg != end) {
            cout << "only some input consumed. Remaining:\n";
            copy(beg, end, ostream_iterator<qi_token<position_t>>(cout, ""));
            return 2;
        }
    } else {
        cout << "parse failed\n";
        return 1;
    }

    stat_reporter rptr;
    for (auto const & r : result)
        boost::apply_visitor(rptr, r);
    std::cout << result.size() << " top-level functions or namespaces, containing:\n";
    rptr.report();

}

#include <boost/wave/cpplexer/re2clex/cpp_re2c_lexer.hpp>
