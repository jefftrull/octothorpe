/**
 *  Example of analyzing equations controlling sections of text in a source file
 *
 *   Copyright (C) 2016 Jeff Trull <edaskel@att.net>
 *
 *   Distributed under the Boost Software License, Version 1.0. (See accompanying
 *   file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
 *
 *
 */

#include <iostream>
#include <iomanip>

#include <boost/spirit/include/lex_plain_token.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix.hpp>
#include <boost/spirit/include/support_istream_iterator.hpp>
#include <boost/fusion/include/adapt_struct.hpp>

#include <boost/wave.hpp>
#include <boost/wave/token_ids.hpp>
#include <boost/wave/cpplexer/cpp_lex_iterator.hpp>

// CVC4 SMT engine includes
#include "cvc4/api/cvc4cpp.h"

// make a Spirit V2-compatible lexer
// analogous to boost::spirit::lex::lexertl::lexer, i.e. LefDefLexer

// we need to wrap cpplexer's tokens so they can be used as Spirit V2 Lex tokens
// compatible with qi::token
template<typename PositionT = boost::wave::util::file_position_type>
class spirit_compatible_token : private boost::wave::cpplexer::lex_token<PositionT>
{
    // pretend to be a lexertl token with one attribute: a string
    // model: lex::lexertl::token<base_string_iter_t, mpl::vector<base_string_t>, mpl::false_>

    typedef typename boost::wave::cpplexer::lex_token<PositionT> base_type;

public:
    typedef typename base_type::string_type base_string_t;
    typedef typename base_type::string_type string_type;
    typedef typename string_type::const_iterator base_string_iter_t;
    typedef          PositionT position_type;

    // requirements from Spirit V2
    typedef boost::wave::token_id id_type;
    typedef base_string_iter_t iterator_type;
    typedef boost::mpl::false_ has_state;
    typedef string_type token_value_type;

    spirit_compatible_token() {}
    spirit_compatible_token(int dummy) : base_type(dummy) {}
    spirit_compatible_token(id_type id, token_value_type value, PositionT pos)
        : base_type(id, value, pos) {}

    id_type id() const {
        return static_cast<base_type const&>(*this);   // via user-defined conversion to id_type
    }
    operator id_type() const { return id(); }

    bool eoi() const {
        return static_cast<base_type const &>(*this).is_eoi();
    }

    // Wave requirements delegated to base class

    bool operator==(spirit_compatible_token const & other) const {
        return static_cast<base_type const &>(*this) == static_cast<base_type const &>(other);
    }

    string_type const & get_value() const {
        return static_cast<base_type const &>(*this).get_value();
    }

    bool is_valid() const {
        return static_cast<base_type const &>(*this).is_valid();
    }

    // Spirit V2 debugging

#if defined(BOOST_SPIRIT_DEBUG)
    friend std::ostream&
    operator<< (std::ostream &os, spirit_compatible_token<PositionT> const & tok) {
        using namespace boost::wave;
        auto id = token_id(tok);
        os << get_token_name(id) << "(";
        if (id == T_NEWLINE) {
            os << "\\n";
        } else {
            os << tok.get_value();
        }
        os << ")" ;
        return os;
    }
#endif
};

//
// Spirit V2 helper function requirements for token (see lex/lexer/lexertl/token.hpp)
//

template <typename Position>
inline bool
token_is_valid(spirit_compatible_token<Position> const & t)
{
    return t.is_valid();
}

//
// Spirit V2 customization points
//

namespace boost { namespace spirit { namespace traits
{

// Let Spirit know how to get data from our token into attributes
template<typename PositionT, typename StringT>
struct assign_to_attribute_from_value<StringT, spirit_compatible_token<PositionT> >
{
    static void 
    call(spirit_compatible_token<PositionT> const & tok, StringT & attr)
    {
        attr = tok.get_value().c_str();
    }
};
template<typename PositionT, typename StringT>
struct assign_to_container_from_value<StringT, spirit_compatible_token<PositionT> >
    : assign_to_attribute_from_value<StringT, spirit_compatible_token<PositionT> >
{};


template<typename PositionT>
struct assign_to_attribute_from_value<boost::iterator_range<char const *>,
                                      spirit_compatible_token<PositionT> >
{
    static void
    call(spirit_compatible_token<PositionT> const & tok,
         boost::iterator_range<char const *> & attr)
    {
        attr = boost::make_iterator_range(tok.get_value().begin(), tok.get_value().end());
    }
};
template<typename PositionT>
struct assign_to_container_from_value<boost::iterator_range<char const *>,
                                      spirit_compatible_token<PositionT> >
    : assign_to_attribute_from_value<boost::iterator_range<char const *>,
                                     spirit_compatible_token<PositionT> >
{};

///////////////////////////////////////////////////////////////////////////
// Overload debug output for a single token, this integrates lexer tokens
// with Qi's simple_trace debug facilities
template <typename PositionT>
struct token_printer_debug<spirit_compatible_token<PositionT> >
{
    typedef spirit_compatible_token<PositionT> token_type;

    template <typename Out>
    static void print(Out& out, token_type const & val)
    {
        out << '[' << val << ']';
    }
};

}}}

// Adapt underlying token iterator from cpplexer (Wave) to one compatible with Spirit V2
// requires adding a special typedef and returning Spirit-compatible tokens
template<typename TokenT>
struct tok_iterator : boost::wave::cpplexer::lex_iterator<TokenT>
{
    using base_type = boost::wave::cpplexer::lex_iterator<TokenT>;
    using position_type = typename TokenT::position_type;

    // add the typedef that qi::token requires
    using base_iterator_type = typename TokenT::string_type::const_iterator;

    // forward constructors
    tok_iterator() {}
    template<typename IteratorT>
    tok_iterator(IteratorT beg, IteratorT end, position_type pos, boost::wave::language_support lang)
        : base_type(beg, end, pos, lang) {}

};

// Parsing will produce text "sections": a set of lines and an associated condition
struct text_section {
    CVC4::api::Term          condition;
    std::vector<std::string> body;
};

BOOST_FUSION_ADAPT_STRUCT(
    text_section,
    (CVC4::api::Term, condition)
    (std::vector<std::string>, body)
)

// Proper use of CVC4 requires caching variables so we don't create two with the same name
struct var_cache {
    var_cache(CVC4::api::Solver& slv) : slv_(slv) {}

    CVC4::api::Term   get_defined_expr(std::string varname) {
        // see if we have cached this variable representing defined(varname)
        auto it = defined_vars_.find(varname);
        if (it != defined_vars_.end()) {
            return it->second;
        }
        // give it a different name than the integer variable representing its value
        CVC4::api::Term var = slv_.mkConst(slv_.getBooleanSort(), varname + "_defined");
        defined_vars_.emplace(varname, var);
        return var;
    }

    // for building integer expressions
    CVC4::api::Term   get_integer_var(std::string varname) {
        // check in cache first
        auto it = int_vars_.find(varname);
        if (it != int_vars_.end()) {
            return it->second;
        }
        CVC4::api::Term var = slv_.mkConst(slv_.getIntegerSort(), varname);
        int_vars_.emplace(varname, var);
        return var;
    }
private:
    CVC4::api::Solver& slv_;
    std::map<std::string, CVC4::api::Term> int_vars_;
    std::map<std::string, CVC4::api::Term> defined_vars_;
};

// Define a simple grammar using our adapted token iterator
template<typename Iterator>
struct skipper : boost::spirit::qi::grammar<Iterator>
{
    skipper() : skipper::base_type(spaces) {
        spaces = +boost::spirit::qi::token(boost::wave::T_SPACE);
    }
private:
    boost::spirit::qi::rule<Iterator> spaces;
};

template<typename Iterator>
struct cond_expr : boost::spirit::qi::grammar<Iterator, CVC4::api::Term(), skipper<Iterator>>
{
    cond_expr(CVC4::api::Solver& slv, var_cache& vars)
        : cond_expr::base_type(bool_expr), slv_(slv), vars_(vars) {
        using boost::spirit::_1;
        using boost::spirit::_3;
        using boost::spirit::_a;
        using boost::spirit::_b;
        using boost::spirit::_r1;
        using boost::spirit::_val;
        using boost::spirit::_pass;
        using boost::spirit::qi::token;
        namespace phx = boost::phoenix;
        using namespace boost::wave;

        cond_inv = ( token(T_NOT) >> bool_term [
                         _val = phx::bind(&cond_expr::create_inverted_expr,
                                          this, _1)]) ;
        ident = token(T_IDENTIFIER);
        defined =  ident [
            _pass = ( _1 == std::string("defined") )
            ]
            >> token(T_LEFTPAREN)
            >> ident [
                _val = phx::bind(&var_cache::get_defined_expr,
                                 &vars_, _1)
                ]
            >> token(T_RIGHTPAREN) ;
        paren_term = token(T_LEFTPAREN)
            >> bool_expr  [_val = _1]
            >> token(T_RIGHTPAREN) ;
        bool_term = cond_inv | defined | paren_term ;

        conj_term = bool_term [ _val = _1 ]
            >> *(token(T_ANDAND) >> bool_term [
                     _val = phx::bind(&cond_expr::create_binary_expr,
                                      this, CVC4::api::AND, _val, _1)]) ;
        disj_term = conj_term [ _val = _1 ]
            >> *(token(T_OROR) >> conj_term [
                     _val = phx::bind(&cond_expr::create_binary_expr,
                                      this, CVC4::api::OR, _val, _1)]) ;

        // parsing a subset of real expressions here, for now
        // we only compare ints, never compute with them
        int_ = token(T_INTLIT) ;
        int_term = ident[_val = phx::bind(&var_cache::get_integer_var,
                                          &vars_, _1)] |
                   int_[_val = phx::bind(&cond_expr::create_integer_const,
                                         this, _1)] ;

        int_comp =
            (int_term >> token(T_EQUAL) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::api::EQUAL, _1, _3) ]
          | (int_term >> token(T_LESS) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::api::LT, _1, _3) ]
          | (int_term >> token(T_GREATER) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::api::GT, _1, _3) ]
          | (int_term >> token(T_LESSEQUAL) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::api::LEQ, _1, _3) ]
          | (int_term >> token(T_GREATEREQUAL) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::api::GEQ, _1, _3) ] ;

        bool_expr = int_comp | disj_term ;

        BOOST_SPIRIT_DEBUG_NODE(ident);
        BOOST_SPIRIT_DEBUG_NODE(defined);
        BOOST_SPIRIT_DEBUG_NODE(bool_term);
        BOOST_SPIRIT_DEBUG_NODE(paren_term);
        BOOST_SPIRIT_DEBUG_NODE(cond_inv);
        BOOST_SPIRIT_DEBUG_NODE(int_term);
        BOOST_SPIRIT_DEBUG_NODE(int_comp);
        BOOST_SPIRIT_DEBUG_NODE(conj_term);
        BOOST_SPIRIT_DEBUG_NODE(disj_term);
        BOOST_SPIRIT_DEBUG_NODE(bool_expr);
    }

private:
    boost::spirit::qi::rule<Iterator, std::string()> ident, int_;
    using expr_rule_t = boost::spirit::qi::rule<Iterator, CVC4::api::Term(), skipper<Iterator>>;
    expr_rule_t defined, cond_inv, bool_term, conj_term, disj_term, int_term, int_comp, paren_term, bool_expr;

    // for building logical expressions
    CVC4::api::Solver& slv_;
    var_cache&         vars_;

    CVC4::api::Term   create_inverted_expr(CVC4::api::Term e) {
        return e.notTerm();
    }
    CVC4::api::Term   create_binary_expr(CVC4::api::Kind op, CVC4::api::Term e1, CVC4::api::Term e2) {
        return slv_.mkTerm(op, e1, e2);
    }
    CVC4::api::Term   create_integer_const(std::string int_literal) {
        return slv_.mkReal(int_literal);  // mkReal encompasses float, integer, and rational
    }
};


template<typename Iterator>
struct cond_grammar : boost::spirit::qi::grammar<Iterator,
                                                 std::vector<text_section>(),
                                                 skipper<Iterator>>
{
    cond_grammar(CVC4::api::Solver& slv, var_cache& vars)
        : cond_grammar::base_type(tunit), slv_(slv), vars_(vars), expr_parser_(slv, vars_) {
        using boost::spirit::_1;
        using boost::spirit::_a;
        using boost::spirit::_b;
        using boost::spirit::_r1;
        using boost::spirit::_val;
        using boost::spirit::qi::token;
        using boost::spirit::qi::omit;
        using boost::spirit::qi::attr;
        using boost::spirit::qi::eps;
        namespace phx = boost::phoenix;
        using namespace boost::wave;

        line_end = token(T_NEWLINE) | token(T_CPPCOMMENT) ;  // Wave absorbs trailing \n

        // semantic action to append string attributes
        auto append = [](auto & dst, auto const & src)
        {
            dst.insert(std::end(dst), std::begin(src), std::end(src));
        };

        textline = (!(token(T_PP_IF) |
                      token(T_PP_IFDEF) |
                      token(T_PP_IFNDEF) |
                      token(T_PP_ELSE) |
                      token(T_PP_ELIF) |
                      token(T_PP_ENDIF)))
            >> *(token - line_end)[phx::bind(append, _val, _1)]
            >> line_end[phx::bind(append, _val, _1)] ;
        textblock = attr(phx::construct<CVC4::api::Term>(_r1)) // conditional for a textblock is just whatever it inherited
            >> +textline ;

        cond_if = token(T_PP_IF)
            >> expr_parser_[_a = _r1, _b = _1] >> line_end
            // both the inherited condition and the new one must be true:
            >>    *basic(phx::bind(&cond_grammar::create_binary_expr,
                                   this, CVC4::api::AND, _a, _b))[
                        phx::bind(append, _val, _1)
                   ]
            // update "condition so far"
            >>    eps[
                _a = phx::bind(&cond_grammar::create_inv_qual_expr,
                               this, _a, _b)
                ]
            >>    *(token(T_PP_ELIF)
                    >> expr_parser_[_b = _1] >> line_end
                    >> *basic(phx::bind(&cond_grammar::create_binary_expr,
                                        this, CVC4::api::AND, _a, _b))[
                            phx::bind(append, _val, _1)
                   ]
                    >> eps[
                        // accumulate condition
                        _a = phx::bind(&cond_grammar::create_inv_qual_expr, this, _a, _b)
                        ])
            >>    -(token(T_PP_ELSE) >> line_end
                    >> *basic(_a)[
                        phx::bind(append, _val, _1)
                    ])
            >>    token(T_PP_ENDIF) >> line_end ;

        ident = token(T_IDENTIFIER);
        cond_ifdef = token(T_PP_IFDEF)
              >>  ident[
                    _a = phx::bind(&var_cache::get_defined_expr, &vars_, _1)
                  ]
              >>  line_end
              >>    *basic(phx::bind(&cond_grammar::create_binary_expr,
                                     this, CVC4::api::AND, _r1, _a))[
                        phx::bind(append, _val, _1)
                    ]
            >>    -(token(T_PP_ELSE) >> line_end
                    >> *basic(phx::bind(&cond_grammar::create_inv_qual_expr,
                                        this, _r1, _a))[
                           phx::bind(append, _val, _1)
                        ])
            >>    token(T_PP_ENDIF) >> line_end ;

        cond_ifndef = token(T_PP_IFNDEF)
            >>    ident[
                _a = phx::bind(&var_cache::get_defined_expr, &vars_, _1)
                ]
            >>    line_end
            >>    *basic(phx::bind(&cond_grammar::create_inv_qual_expr,
                                   this, _r1, _a))[
                       phx::bind(append, _val, _1)
                    ]
            >>    -(token(T_PP_ELSE) >> line_end
                    >> *basic(phx::bind(&cond_grammar::create_binary_expr,
                                        this, CVC4::api::AND, _r1, _a))[
                            phx::bind(append, _val, _1)
                        ])
            >>    token(T_PP_ENDIF) >> line_end ;

        basic = textblock(_r1) | cond_if(_r1) | cond_ifdef(_r1) | cond_ifndef(_r1);

        toplvl = basic(phx::bind(&cond_grammar::create_boolean_const,
                                this, true))
            >> -toplvl ;
        tunit = toplvl >> omit[token(T_EOF)] ;

        BOOST_SPIRIT_DEBUG_NODE(tunit);
        BOOST_SPIRIT_DEBUG_NODE(toplvl);
        BOOST_SPIRIT_DEBUG_NODE(basic);
        BOOST_SPIRIT_DEBUG_NODE(ident);
        BOOST_SPIRIT_DEBUG_NODE(textline);
        BOOST_SPIRIT_DEBUG_NODE(line_end);
        BOOST_SPIRIT_DEBUG_NODE(textblock);

        BOOST_SPIRIT_DEBUG_NODE(cond_if);
        BOOST_SPIRIT_DEBUG_NODE(cond_ifdef);
        BOOST_SPIRIT_DEBUG_NODE(cond_ifndef);

    }

private:
    boost::spirit::qi::rule<Iterator, std::string()> ident;
    boost::spirit::qi::rule<Iterator, std::string()> line_end;
    boost::spirit::qi::rule<Iterator, std::string()> textline;   // no skipper! Keep as-is.
    // a textblock is a single section of non-conditional lines
    boost::spirit::qi::rule<Iterator, text_section(CVC4::api::Term)> textblock;

    boost::spirit::qi::rule<Iterator, std::vector<text_section>(), skipper<Iterator>> tunit, toplvl;
    boost::spirit::qi::rule<Iterator, std::vector<text_section>(CVC4::api::Term), skipper<Iterator>>
        basic;

    // cond_ifdef/cond_ifndef need an attribute for remembering the macro name
    boost::spirit::qi::rule<Iterator, std::vector<text_section>(CVC4::api::Term), skipper<Iterator>,
                            boost::spirit::locals<CVC4::api::Term>> cond_ifdef, cond_ifndef;

    // cond_if needs a local attribute for remembering conditions, and one for
    // accumulating conditions from elif's
    boost::spirit::qi::rule<Iterator, std::vector<text_section>(CVC4::api::Term), skipper<Iterator>,
                            boost::spirit::locals<CVC4::api::Term, CVC4::api::Term>> cond_if;

    // for building logical expressions
    CVC4::api::Solver&  slv_;
    var_cache&          vars_;
    cond_expr<Iterator> expr_parser_;

    CVC4::api::Term   create_binary_expr(CVC4::api::Kind op, CVC4::api::Term e1, CVC4::api::Term e2) {
        return slv_.mkTerm(op, e1, e2);
    }
    // e1 && !e2
    // useful for "else" clauses
    CVC4::api::Term   create_inv_qual_expr(CVC4::api::Term e1, CVC4::api::Term e2) {
        return e1.andTerm(e2.notTerm());
    }
    CVC4::api::Term   create_boolean_const(bool b) {
        return slv_.mkBoolean(b);
    }
};

int main(int argc, char **argv) {
    using namespace std;
    using namespace boost::wave;

    if ((argc == 1) || (argc > 3)) {
        cerr << "usage: " << argv[0] << " [condition] path\n";
        return 4;
    }

    char const* fn = ((argc == 2) ? argv[1] : argv[2]);
    ifstream cppfile(fn);
    if (!cppfile.is_open()) {
        cerr << "unable to open requested file " << fn << "\n";
        return 5;
    }
    cppfile.unsetf(ios::skipws);
    boost::spirit::istream_iterator fbeg(cppfile);

    // Give it a try
    using token_t = spirit_compatible_token<>;
    using position_t = token_t::position_type;
    position_t pos(fn);

    // create Spirit V2-compatible lexer token iterators from character iterators
    using cpplexer_iterator_t = tok_iterator<token_t>;
    cpplexer_iterator_t beg(fbeg, boost::spirit::istream_iterator(), pos,
                               language_support(support_cpp|support_cpp0x));
    cpplexer_iterator_t end;

    CVC4::api::Solver slv;
    var_cache         vars(slv);     // global so we can share with user expression parser
    cond_grammar<decltype(beg)> fileparser(slv, vars);
    vector<text_section> result;
    auto start = beg;
    bool pass = boost::spirit::qi::phrase_parse(beg, end, fileparser,
                                                skipper<decltype(beg)>(), result);
    if (pass) {
        if (beg == start) {
            cout << "no input consumed!\n";
            return 2;
        } else if (beg != end) {
            cout << "only some input consumed. Remaining:\n";
            copy(beg, end, ostream_iterator<spirit_compatible_token<position_t>>(cout, ""));
            return 2;
        }
        // make an assertion for the user input, if present
        if (argc == 3) {
            // an expression was supplied
            string expr(argv[1]);
            position_t epos("command-line input");
            cpplexer_iterator_t ebeg(expr.begin(), expr.end(), pos,
                                        language_support(support_cpp|support_cpp0x));
            cpplexer_iterator_t eend;

            cond_expr<decltype(ebeg)> exprparser(slv, vars);
            CVC4::api::Term user_expr;
            pass = boost::spirit::qi::phrase_parse(ebeg, eend, exprparser,
                                                   skipper<decltype(ebeg)>(), user_expr);
            if (!pass)
            {
                std::cerr << "error parsing assume-expression \"" << argv[1] << "\"\n";
                return 3;
            }
            slv.assertFormula(user_expr);
        }

        for (auto const & s : result) {
            if (slv.checkSatAssuming(s.condition).isUnsat()) {
                cout << "detected a dead code section with condition ";
                cout << slv.simplify(s.condition) << ":\n";
                copy(s.body.begin(), s.body.end(),
                     ostream_iterator<string>(cout, ""));
            }
        }
    } else {
        cout << "parse failed\n";
        return 1;
    }
    return 0;
}

#include <boost/wave/cpplexer/re2clex/cpp_re2c_lexer.hpp>
