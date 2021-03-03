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

// attribute for if statements
BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    (),
    if_stmt_t,
    (Position, kwd)                         // location of "if"
    (Position, stmt)                        // location of true branch statement
    (boost::optional<Position>, else_stmt)  // location of else clause, if present
)

// attribute for while loops
BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    (),
    while_stmt_t,
    (Position, kwd)    // where we found "while"
    (Position, stmt)   // where first token of action is (left brace or plain stmt)
)

// and for for loops
BOOST_FUSION_DEFINE_TPL_STRUCT(
    (Position),
    (),
    for_stmt_t,
    (Position, kwd)    // where we found "for"
    (Position, stmt)   // where first token of action is (left brace or plain stmt)
)

#ifdef BOOST_SPIRIT_DEBUG
// print helpers
namespace std {

template<typename Position>
std::ostream &
operator<<(std::ostream& os, if_stmt_t<Position> const & v)
{
    os << "IF: " << v.kwd << ", " << v.stmt;
    if (v.else_stmt)
        os << " ELSE: " << *v.else_stmt;
    return os;
}

template<typename Position>
std::ostream &
operator<<(std::ostream& os, while_stmt_t<Position> const & v)
{
    os << "WHILE: " << v.kwd << ", " << v.stmt;
    return os;
}

template<typename Position>
std::ostream &
operator<<(std::ostream& os, for_stmt_t<Position> const & v)
{
    os << "FOR: " << v.kwd << ", " << v.stmt;
    return os;
}

}



#endif // BOOST_SPIRIT_DEBUG

template<typename Position>
using stmt_structure_t = boost::variant<if_stmt_t<Position>,
                                        while_stmt_t<Position>,
                                        for_stmt_t<Position>>;

template<typename Iterator>
struct cpp_indent : boost::spirit::qi::grammar<Iterator, skipper<Iterator>,
                                               std::vector<stmt_structure_t<typename Iterator::position_type>>()>
{
    cpp_indent() : cpp_indent::base_type(cppfile)
    {
        using namespace boost::wave;
        using namespace boost::spirit;
        namespace phx = boost::phoenix;
        using qi::token;
        using qi::omit;

        qi::as<position_t> as_position;
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

        // an expression is a series of tokens not including semicolons,
        // with balanced parens/braces
        // its attribute is the position of the first token
        plain_expr_tok =
            (any_token - token(T_SEMICOLON)
             - token(T_LEFTPAREN) - token(T_LEFTBRACE)
             - token(T_RIGHTPAREN) - token(T_RIGHTBRACE)) ;

        // TODO: remove as_position from as many points as possible
        // tokens are compatible with positions already - using "omit"
        // on the unneeded parts may be a cleaner approach

        expr =
            (as_position[token(T_LEFTPAREN)][_val = _1] >> expr >> token(T_RIGHTPAREN)) |
            (as_position[token(T_LEFTBRACE)][_val = _1] >> expr >> token(T_RIGHTBRACE)) |
            // function call - does not cover all possibilities, just plain identifier:
            (as_position[token(T_IDENTIFIER)][_val = _1] >>
             token(T_LEFTPAREN) >> -expr >> token(T_RIGHTPAREN)) |
            (plain_expr_tok[_val = _1] >> *plain_expr_tok) ;

        stmt = (as_position[token(T_LEFTBRACE)][_val = _1] >> *stmt >> token(T_RIGHTBRACE)) |
            // semicolon-terminated expression. We use the position of the first token
            ( as_position[token(T_SEMICOLON)][_val = _1] |  // empty statement
              (expr[_val = _1] >> *expr >> token(T_SEMICOLON) )) ;

        // so here we need to collect different stats if there's a braced expression,
        // and if there's a newline before or after the left brace
        // the stats need to include 1) braced or not 2) newline or not 3) indentation vs. "if"

        if_stmt = token(T_IF) >>
            omit[token(T_LEFTPAREN) >> expr >> token(T_RIGHTPAREN)] >>
            stmt >>
            -(omit[token(T_ELSE)] >> stmt) ;

        while_stmt = token(T_WHILE) >>
            omit[ token(T_LEFTPAREN) >> expr >> token(T_RIGHTPAREN) ] >>
            stmt ;

        for_stmt = token(T_FOR) >>
            omit[token(T_LEFTPAREN) >>
                 -expr >> token(T_SEMICOLON) >>
                 -expr >> token(T_SEMICOLON) >>
                 -expr >> token(T_RIGHTPAREN)] >>
            stmt ;

        // BOZO insert token consumer rule

        cppfile = *(if_stmt | while_stmt | for_stmt) >> omit[token(T_EOF)];

        BOOST_SPIRIT_DEBUG_NODE(any_token);
        BOOST_SPIRIT_DEBUG_NODE(if_stmt);
        BOOST_SPIRIT_DEBUG_NODE(while_stmt);
        BOOST_SPIRIT_DEBUG_NODE(for_stmt);
        BOOST_SPIRIT_DEBUG_NODE(plain_expr_tok);
        BOOST_SPIRIT_DEBUG_NODE(expr);
        BOOST_SPIRIT_DEBUG_NODE(stmt);
        BOOST_SPIRIT_DEBUG_NODE(cppfile);

    }
private:
    using position_t = typename Iterator::position_type;
    boost::spirit::qi::rule<Iterator, skipper<Iterator>,
                            std::vector<stmt_structure_t<position_t>>() > cppfile;
    boost::spirit::qi::rule<Iterator, skipper<Iterator>, position_t() > plain_expr_tok;
    boost::spirit::qi::rule<Iterator, skipper<Iterator>, position_t() > expr;
    boost::spirit::qi::rule<Iterator, skipper<Iterator>, position_t() > stmt;

    boost::spirit::qi::rule<Iterator, skipper<Iterator>, if_stmt_t<position_t>() > if_stmt;
    boost::spirit::qi::rule<Iterator, skipper<Iterator>, while_stmt_t<position_t>() > while_stmt;
    boost::spirit::qi::rule<Iterator, skipper<Iterator>, for_stmt_t<position_t>() > for_stmt;
    boost::spirit::qi::rule<Iterator, skipper<Iterator>, position_t() > any_token;
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
    auto start = beg;
    bool pass = boost::spirit::qi::phrase_parse(beg, end, fileparser,
                                                skipper<decltype(beg)>());
    if (pass) {
        if (beg == start) {
            cout << "no input consumed!\n";
            return 2;
        } else if (beg != end) {
            cout << "only some input consumed. Remaining:\n";
            copy(beg, end, ostream_iterator<qi_token<position_t>>(cout, ""));
            return 2;
        }
        return 0;
    } else {
        cout << "parse failed\n";
        return 1;
    }
}

#include <boost/wave/cpplexer/re2clex/cpp_re2c_lexer.hpp>
