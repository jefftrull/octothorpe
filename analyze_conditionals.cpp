/**
 * Example of turning conditional compilation into policy classes
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

#include <boost/wave.hpp>
#include <boost/wave/token_ids.hpp>
#include <boost/wave/cpplexer/cpp_lex_token.hpp>
#include <boost/wave/cpplexer/cpp_lex_iterator.hpp>

#include <boost/spirit/include/lex_lexertl.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix.hpp>

// make a Spirit V2-compatible lexer
// analogous to boost::spirit::lex::lexertl::lexer, i.e. LefDefLexer

// lexertl::lexer takes a template argument Token, which is a typedef
// specialization of position_token with underlying iterator and
// possible token values specified

template<typename CharIterator>
struct spirit_cpp_lexer {
    typedef boost::wave::cpplexer::lex_token<> token_type;
    typedef boost::wave::cpplexer::lex_iterator<token_type> iterator_type;
    typedef boost::wave::token_id token_id;

    iterator_type begin(CharIterator& first, CharIterator const & last,
                        char const* initial_state = 0) const {
        token_type::position_type pos("unknown.cpp");
        using namespace boost::wave;
        return iterator_type(first, last, pos,
                             language_support(support_cpp|support_cpp0x));
    }
    iterator_type end() const {
        return spirit_cpp_lexer::iterator_type();
    }
};
        
// we need to wrap cpplexer's tokens so they can be used as Spirit V2 Lex tokens
// compatible with qi::token
struct spirit_compatible_token {
    // requirements from Spirit V2
    typedef boost::wave::token_id id_type;
    id_type id() const {
        return base_token_;   // via user-defined conversion to id_type
    }

    spirit_compatible_token(boost::wave::cpplexer::lex_token<> base_token)
        : base_token_(base_token) {}
    spirit_compatible_token() {}

    std::string value() const {
        return base_token_.get_value().c_str();
    }

private:
    boost::wave::cpplexer::lex_token<> base_token_;
};

// Let Spirit know how to get data from our token into attributes
namespace boost { namespace spirit { namespace traits
{
// a specialization for our token - only for std::string.  Possible to generalize...
template <>
struct assign_to_container_from_value<std::string, spirit_compatible_token>
{
    static void 
    call(spirit_compatible_token const& tok, std::string& attr)
    {
        attr = tok.value();
    }
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

// Define a simple grammar using the above
template<typename Iterator>
struct cond_grammar : boost::spirit::qi::grammar<Iterator, std::string()>
{
    cond_grammar()
        : cond_grammar::base_type(start) {
        using boost::spirit::_1;
        using boost::spirit::_val;
        using boost::spirit::qi::token;
        using namespace boost::wave;
        start = token(T_PP_IFDEF) >> token(T_SPACE) >> ident[_val = _1] >> token(T_NEWLINE);
        ident = token(T_IDENTIFIER);
    }
private:
    boost::spirit::qi::rule<Iterator, std::string()> start;
    boost::spirit::qi::rule<Iterator, std::string()> ident;
};

int main() {
    using namespace std;
    using namespace boost::wave;

    string testprog(
        "#ifdef FOO\n"
        "#include <string>\n"
        "#ifndef BAR\n"
        "using string_t = std::string;\n"
        "#else\n"
        "using string_t = char*;\n"
        "#endif\n"
        "#if !defined(FOO)"
        "using string_t = QString;  // dead code\n"
        "#endif\n"
        "#endif\n"
        );

    // give it a try
    using lexer_t = spirit_cpp_lexer<string::const_iterator>;
    lexer_t::token_type::position_type pos("testprog.cpp");
    lexer_t::iterator_type beg(testprog.begin(), testprog.end(), pos,
                               language_support(support_cpp|support_cpp0x));
    lexer_t::iterator_type end;

    auto xbeg = make_tok_iterator(beg);
    auto xend = make_tok_iterator(end);
    cond_grammar<decltype(xbeg)> myparser;
    std::string result;
    bool pass = boost::spirit::qi::parse(xbeg, xend, myparser, result);
    if (pass) {
        std::cout << "parse successful\n";
        std::cout << "collected identifier " << result << "\n";
        if (xbeg == make_tok_iterator(beg)) {
            std::cout << "no input consumed!\n";
        } else if (xbeg == make_tok_iterator(end)) {
            std::cout << "all input consumed!\n";
        } else {
            std::cout << "some input consumed\n";
        }
    } else {
        std::cout << "parse failed\n";
    }

}
