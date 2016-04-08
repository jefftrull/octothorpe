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

#include <boost/iterator/transform_iterator.hpp>

// make a Spirit V2-compatible lexer
// analogous to boost::spirit::lex::lexertl::lexer, i.e. LefDefLexer

// lexertl::lexer takes a template argument Token, which is a typedef
// specialization of position_token with underlying iterator and
// possible token values specified

// Observation: the grammars do not use their Lexer template parameter!
// Only DefTokens does
// Maybe we can try defining a grammar this way
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
private:
    boost::wave::cpplexer::lex_token<> base_token_;
};

// also need to adapt lex_iterator<token_type> to produce an iterator
// over our wrapped token type

template<typename Iterator>
struct cond_grammar : boost::spirit::qi::grammar<Iterator>
{
    cond_grammar()
        : cond_grammar::base_type(start) {
        using namespace boost::spirit::qi;
        using namespace boost::wave;
        start = token(T_PP_IFDEF) >> token(T_SPACE) >> token(T_IDENTIFIER) >> token(T_NEWLINE);
    }
private:
    boost::spirit::qi::rule<Iterator> start;
};

// class to convert underlying cpplexer tokens to Spirit V2-compatible tokens
// we do this instead of a lambda because our iterator must return references
// to be forward category, which is required by Spirit
struct tok_transformer
{
    spirit_compatible_token const& operator()(boost::wave::cpplexer::lex_token<> const& tok) const
    {
        result_ = spirit_compatible_token(tok);
        return result_;
    }
private:
    spirit_compatible_token mutable result_;   // BOZO don't like this, need a better solution
};

template<typename BaseIterator>
struct tok_iterator :
    boost::iterator_adaptor<tok_iterator<BaseIterator>,
                            boost::transform_iterator<tok_transformer, BaseIterator>>
{
    // add a typedef qi::token requires
    using base_iterator_type = BaseIterator;

    // forward constructor to parent
    tok_iterator(BaseIterator it, tok_transformer t)
        : tok_iterator::iterator_adaptor_(
            typename tok_iterator::iterator_adaptor::base_type(it, t)) {}
};

template<typename BaseIterator>
tok_iterator<BaseIterator>
make_tok_iterator(BaseIterator it, tok_transformer t) {
    return tok_iterator<BaseIterator>(it, t);
}

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

    tok_transformer transformer;
    auto xbeg = make_tok_iterator(beg, transformer);
    auto xend = make_tok_iterator(end, transformer);
    cond_grammar<decltype(xbeg)> myparser;
    bool result = boost::spirit::qi::parse(xbeg, xend, myparser);
    if (result) {
        std::cout << "parse successful\n";
        if (xbeg == make_tok_iterator(beg, transformer)) {
            std::cout << "no input consumed!\n";
        } else if (xbeg == make_tok_iterator(end, transformer)) {
            std::cout << "all input consumed!\n";
        } else {
            std::cout << "some input consumed\n";
        }
    } else {
        std::cout << "parse failed\n";
    }

}
