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

#include <boost/spirit/include/lex_lexertl.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix.hpp>
#include <boost/spirit/include/support_istream_iterator.hpp>
#include <boost/fusion/include/adapt_struct.hpp>

#include <boost/wave.hpp>
#include <boost/wave/token_ids.hpp>
#include <boost/wave/cpplexer/cpp_lex_token.hpp>
#include <boost/wave/cpplexer/cpp_lex_iterator.hpp>

// CVC4 SMT engine includes
#include "cvc4/smt/smt_engine.h"

// make a Spirit V2-compatible lexer
// analogous to boost::spirit::lex::lexertl::lexer, i.e. LefDefLexer

typedef boost::wave::cpplexer::lex_token<> cpplexer_token_t;
typedef boost::wave::cpplexer::lex_iterator<cpplexer_token_t> cpplexer_iterator_t;

// we need to wrap cpplexer's tokens so they can be used as Spirit V2 Lex tokens
// compatible with qi::token
struct spirit_compatible_token {
    typedef boost::wave::cpplexer::lex_token<>::string_type base_string_t;
    typedef base_string_t::const_iterator base_string_iter_t;

    // requirements from Spirit V2
    typedef boost::wave::token_id id_type;
    id_type id() const {
        return base_token_;   // via user-defined conversion to id_type
    }

    spirit_compatible_token(boost::wave::cpplexer::lex_token<> base_token)
        : base_token_(base_token) {}
    spirit_compatible_token() {}

    boost::iterator_range<base_string_t::const_iterator> value() const {
        return boost::iterator_range<base_string_iter_t>(begin(), end());
    }

    bool eoi() const {
        return base_token_.is_eoi();
    }

    // provide two methods and a typedef so we can pretend to be a string
    // this allows rules to concatenate token values together without
    // extra Phoenix verbiage
    base_string_iter_t begin() const {
        return base_token_.get_value().begin();
    }
    base_string_iter_t end() const {
        return base_token_.get_value().end();
    }
    typedef base_string_t::const_iterator const_iterator;
            

private:
    boost::wave::cpplexer::lex_token<> base_token_;

    friend std::ostream&
    operator<< (std::ostream &os, spirit_compatible_token const& tok) {
        using namespace boost::wave;
        auto id = token_id(tok.base_token_);
        os << get_token_name(id) << "(";
        if (id == T_NEWLINE) {
            os << "\\n";
        } else {
            os << tok.value();
        }
        os << ")" ;
        return os;
    }
};

// Help with debug by defining an operator so that a loop in simple_trace.hpp works
#ifdef BOOST_SPIRIT_DEBUG
bool operator&&(bool a, spirit_compatible_token const& tok) {
    return a && !tok.eoi();
}
#endif

// Let Spirit know how to get data from our token into attributes
namespace boost { namespace spirit { namespace traits
{

template<>
struct assign_to_container_from_value<
    boost::iterator_range<spirit_compatible_token::base_string_iter_t>,
    spirit_compatible_token>
{
    static void 
    call(spirit_compatible_token const& tok,
         boost::iterator_range<spirit_compatible_token::base_string_iter_t>& attr)
    {
        attr = tok.value();
    }
};

template<>
struct is_string<spirit_compatible_token> : mpl::true_ {};

template<>
struct is_container<spirit_compatible_token> : mpl::true_ {};

template<>
struct char_type_of<spirit_compatible_token> {
    typedef spirit_compatible_token::base_string_t::value_type type;
};

}}}


// Adapt underlying token iterator from cpplexer (Wave) to one compatible with Spirit V2
// requires adding a special typedef and returning Spirit-compatible tokens
template<typename BaseIterator>
struct tok_iterator :
    boost::iterator_adaptor<tok_iterator<BaseIterator>,
                            BaseIterator,
                            spirit_compatible_token,        // value type
                            std::forward_iterator_tag,      // category we expect
                            spirit_compatible_token const&> // reference type
{
    // add the typedef that qi::token requires
    // this is actually the really really underlying one, i.e. character
    // not just the one we are wrapping here
    using base_iterator_type = typename BaseIterator::token_type::string_type::const_iterator;

    tok_iterator();

    tok_iterator(BaseIterator it) : tok_iterator::iterator_adaptor_(it) {}

private:
    friend class boost::iterator_core_access;

    spirit_compatible_token const& dereference() const {
        result_ = spirit_compatible_token(
            *tok_iterator::iterator_adaptor_::base_reference());
        return result_;
    }

    spirit_compatible_token mutable result_;
};

template<typename BaseIterator>
tok_iterator<BaseIterator>
make_tok_iterator(BaseIterator it) {
    return tok_iterator<BaseIterator>(it);
}

// Parsing will produce text "sections": a set of lines and an associated condition
struct text_section {
    CVC4::Expr               condition;
    std::vector<std::string> body;
};

BOOST_FUSION_ADAPT_STRUCT(
    text_section,
    (CVC4::Expr, condition)
    (std::vector<std::string>, body)
)

// Proper use of CVC4 requires caching variables so we don't create two with the same name
struct var_cache {
    var_cache(CVC4::ExprManager& em) : em_(em) {}

    CVC4::Expr   get_defined_expr(std::string varname) {
        // see if we have cached this variable representing defined(varname)
        auto it = defined_vars_.find(varname);
        if (it != defined_vars_.end()) {
            return it->second;
        }
        // give it a different name than the integer variable representing its value
        CVC4::Expr var = em_.mkVar(varname + "_defined", em_.booleanType());
        defined_vars_.emplace(varname, var);
        return var;
    }

    // for building integer expressions
    CVC4::Expr   get_integer_var(std::string varname) {
        // check in cache first
        auto it = int_vars_.find(varname);
        if (it != int_vars_.end()) {
            return it->second;
        }
        CVC4::Expr var = em_.mkVar(varname, em_.integerType());
        int_vars_.emplace(varname, var);
        return var;
    }
private:
    CVC4::ExprManager& em_;
    std::map<std::string, CVC4::Expr> int_vars_;
    std::map<std::string, CVC4::Expr> defined_vars_;
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
struct cond_expr : boost::spirit::qi::grammar<Iterator, CVC4::Expr(), skipper<Iterator>>
{
    cond_expr(CVC4::ExprManager& em, var_cache& vars)
        : cond_expr::base_type(bool_expr), em_(em), vars_(vars) {
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
                                      this, CVC4::kind::AND, _val, _1)]) ;
        disj_term = conj_term [ _val = _1 ]
            >> *(token(T_OROR) >> conj_term [
                     _val = phx::bind(&cond_expr::create_binary_expr,
                                      this, CVC4::kind::OR, _val, _1)]) ;

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
                                 this, CVC4::kind::EQUAL, _1, _3) ]
          | (int_term >> token(T_LESS) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::kind::LT, _1, _3) ]
          | (int_term >> token(T_GREATER) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::kind::GT, _1, _3) ]
          | (int_term >> token(T_LESSEQUAL) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::kind::LEQ, _1, _3) ]
          | (int_term >> token(T_GREATEREQUAL) >> int_term) [
                _val = phx::bind(&cond_expr::create_binary_expr,
                                 this, CVC4::kind::GEQ, _1, _3) ] ;

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
    using expr_rule_t = boost::spirit::qi::rule<Iterator, CVC4::Expr(), skipper<Iterator>>;
    expr_rule_t defined, cond_inv, bool_term, conj_term, disj_term, int_term, int_comp, paren_term, bool_expr;

    // for building logical expressions
    CVC4::ExprManager& em_;
    var_cache&         vars_;

    CVC4::Expr   create_inverted_expr(CVC4::Expr e) {
        return e.notExpr();
    }
    CVC4::Expr   create_binary_expr(CVC4::Kind op, CVC4::Expr e1, CVC4::Expr e2) {
        return em_.mkExpr(op, e1, e2);
    }
    CVC4::Expr   create_integer_const(std::string int_literal) {
        return em_.mkConst(CVC4::Rational(int_literal));
    }
};


template<typename Iterator>
struct cond_grammar : boost::spirit::qi::grammar<Iterator,
                                                 std::vector<text_section>(),
                                                 skipper<Iterator>>
{
    cond_grammar(CVC4::ExprManager& em, var_cache& vars)
        : cond_grammar::base_type(tunit), em_(em), vars_(vars), expr_parser_(em, vars_) {
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

        textline = (!(token(T_PP_IF) |
                      token(T_PP_IFDEF) |
                      token(T_PP_IFNDEF) |
                      token(T_PP_ELSE) |
                      token(T_PP_ELIF) |
                      token(T_PP_ENDIF)))
            >> *(token - line_end) >> line_end ;
        textblock = attr(phx::construct<CVC4::Expr>(_r1)) // conditional for a textblock is just whatever it inherited
            >> +textline ;

        cond_if = token(T_PP_IF)
            >> expr_parser_[_a = _r1, _b = _1] >> line_end
            // both the inherited condition and the new one must be true:
            >>    *basic(phx::bind(&cond_grammar::create_binary_expr,
                                   this, CVC4::kind::AND, _a, _b))[
                        phx::insert(_val, phx::end(_val), phx::begin(_1), phx::end(_1))
                   ]
            // update "condition so far"
            >>    eps[
                _a = phx::bind(&cond_grammar::create_inv_qual_expr,
                               this, _a, _b)
                ]
            >>    *(token(T_PP_ELIF)
                    >> expr_parser_[_b = _1] >> line_end
                    >> *basic(phx::bind(&cond_grammar::create_binary_expr,
                                        this, CVC4::kind::AND, _a, _b))[
                            phx::insert(_val, phx::end(_val), phx::begin(_1), phx::end(_1))
                   ]
                    >> eps[
                        // accumulate condition
                        _a = phx::bind(&cond_grammar::create_inv_qual_expr, this, _a, _b)
                        ])
            >>    -(token(T_PP_ELSE) >> line_end
                    >> *basic(_a)[
                        phx::insert(_val, phx::end(_val), phx::begin(_1), phx::end(_1))
                    ])
            >>    token(T_PP_ENDIF) >> line_end ;

        ident = token(T_IDENTIFIER);
        cond_ifdef = token(T_PP_IFDEF)
              >>  ident[
                    _a = phx::bind(&var_cache::get_defined_expr, &vars_, _1)
                  ]
              >>  line_end
              >>    *basic(phx::bind(&cond_grammar::create_binary_expr,
                                     this, CVC4::kind::AND, _r1, _a))[
                        phx::insert(_val, phx::end(_val), phx::begin(_1), phx::end(_1))
                    ]
            >>    -(token(T_PP_ELSE) >> line_end
                    >> *basic(phx::bind(&cond_grammar::create_inv_qual_expr,
                                        this, _r1, _a))[
                           phx::insert(_val, phx::end(_val), phx::begin(_1), phx::end(_1))
                        ])
            >>    token(T_PP_ENDIF) >> line_end ;

        cond_ifndef = token(T_PP_IFNDEF)
            >>    ident[
                _a = phx::bind(&var_cache::get_defined_expr, &vars_, _1)
                ]
            >>    line_end
            >>    *basic(phx::bind(&cond_grammar::create_inv_qual_expr,
                                   this, _r1, _a))[
                       phx::insert(_val, phx::end(_val), phx::begin(_1), phx::end(_1))
                    ]
            >>    -(token(T_PP_ELSE) >> line_end
                    >> *basic(phx::bind(&cond_grammar::create_binary_expr,
                                        this, CVC4::kind::AND, _r1, _a))[
                            phx::insert(_val, phx::end(_val), phx::begin(_1), phx::end(_1))
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

        BOOST_SPIRIT_DEBUG_NODE(expr_parser_);
        BOOST_SPIRIT_DEBUG_NODE(cond_if);
        BOOST_SPIRIT_DEBUG_NODE(cond_ifdef);
        BOOST_SPIRIT_DEBUG_NODE(cond_ifndef);

    }

private:
    boost::spirit::qi::rule<Iterator, std::string()> ident;
    boost::spirit::qi::rule<Iterator, std::string()> line_end;
    boost::spirit::qi::rule<Iterator, std::string()> textline;   // no skipper! Keep as-is.
    // a textblock is a single section of non-conditional lines
    boost::spirit::qi::rule<Iterator, text_section(CVC4::Expr)> textblock;

    boost::spirit::qi::rule<Iterator, std::vector<text_section>(), skipper<Iterator>> tunit, toplvl;
    boost::spirit::qi::rule<Iterator, std::vector<text_section>(CVC4::Expr), skipper<Iterator>>
        basic;

    // cond_ifdef/cond_ifndef need an attribute for remembering the macro name
    boost::spirit::qi::rule<Iterator, std::vector<text_section>(CVC4::Expr), skipper<Iterator>,
                            boost::spirit::locals<CVC4::Expr>> cond_ifdef, cond_ifndef;

    // cond_if needs a local attribute for remembering conditions, and one for
    // accumulating conditions from elif's
    boost::spirit::qi::rule<Iterator, std::vector<text_section>(CVC4::Expr), skipper<Iterator>,
                            boost::spirit::locals<CVC4::Expr, CVC4::Expr>> cond_if;

    // for building logical expressions
    CVC4::ExprManager&  em_;
    var_cache&          vars_;
    cond_expr<Iterator> expr_parser_;

    CVC4::Expr   create_binary_expr(CVC4::Kind op, CVC4::Expr e1, CVC4::Expr e2) {
        return em_.mkExpr(op, e1, e2);
    }
    // e1 && !e2
    // useful for "else" clauses
    CVC4::Expr   create_inv_qual_expr(CVC4::Expr e1, CVC4::Expr e2) {
        return e1.andExpr(e2.notExpr());
    }
    CVC4::Expr   create_boolean_const(bool b) {
        return em_.mkConst(b);
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
    cpplexer_token_t::position_type pos(fn);

    // create lexer token iterators from character iterators
    cpplexer_iterator_t beg(fbeg, boost::spirit::istream_iterator(), pos,
                               language_support(support_cpp|support_cpp0x));
    cpplexer_iterator_t end;

    // create Spirit V2-compatible iterators from lexer iterators
    auto xbeg = make_tok_iterator(beg);
    auto xend = make_tok_iterator(end);
    CVC4::ExprManager em;
    CVC4::SmtEngine   smt(&em);
    var_cache         vars(em);      // global so we can share with user expression parser
    cond_grammar<decltype(xbeg)> fileparser(em, vars);
    vector<text_section> result;
    bool pass = boost::spirit::qi::phrase_parse(xbeg, xend, fileparser,
                                                skipper<decltype(xbeg)>(), result);
    if (pass) {
        if (xbeg == make_tok_iterator(beg)) {
            cout << "no input consumed!\n";
            return 2;
        } else if (xbeg != make_tok_iterator(end)) {
            cout << "only some input consumed. Remaining:\n";
            copy(xbeg, xend, ostream_iterator<spirit_compatible_token>(cout, ""));
            return 2;
        }
        // make an assertion for the user input, if present
        if (argc == 3) {
            // an expression was supplied
            string expr(argv[1]);
            cpplexer_token_t::position_type epos("command-line input");
            cpplexer_iterator_t ebeg(expr.begin(), expr.end(), pos,
                                        language_support(support_cpp|support_cpp0x));
            cpplexer_iterator_t eend;
            auto xebeg = make_tok_iterator(ebeg);
            auto xeend = make_tok_iterator(eend);
            cond_expr<decltype(xebeg)> exprparser(em, vars);
            CVC4::Expr user_expr;
            pass = boost::spirit::qi::phrase_parse(xebeg, xeend, exprparser,
                                                   skipper<decltype(xebeg)>(), user_expr);
            smt.assertFormula(user_expr);
        }

        for (auto const& s : result) {
            if (smt.checkSat(s.condition) != CVC4::Result::SAT) {
                cout << "detected a dead code section with condition ";
                cout << smt.simplify(s.condition) << ":\n";
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
