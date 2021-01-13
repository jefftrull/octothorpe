// Support for Spirit V2 (Qi) parsing with Wave tokens
//  Copyright (c) 2021      Jeffrey Trull
//  Copyright (c) 2001-2012 Hartmut Kaiser
//
//  Distributed under the Boost Software License, Version 1.0. (See accompanying
//  file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#include <boost/spirit/include/lex_plain_token.hpp>
#include <boost/spirit/include/qi.hpp>

#include <boost/wave/cpplexer/cpp_lex_iterator.hpp>
#include <boost/wave/token_ids.hpp>
#include <boost/wave/util/file_position.hpp>

#include <utility>

// we need to wrap cpplexer's tokens so they can be used as Spirit V2 Lex
// tokens compatible with qi::token
template<typename PositionT = boost::wave::util::file_position_type>
class qi_token : private boost::wave::cpplexer::lex_token<PositionT>
{
    // pretend to be a lexertl token with flexible attributes
    // model: lex::lexertl::token<base_string_iter_t,
    //                            mpl::vector<base_string_t, PositionT>,
    //                            mpl::false_>

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
    typedef std::pair<string_type, position_type> token_value_type;

    qi_token() {}
    qi_token(int dummy) : base_type(dummy) {}
    qi_token(id_type id, string_type const & value, PositionT pos)
        : base_type(id, value, pos) {}

    id_type id() const {
        // apply user-defined conversion to id_type
        return static_cast<base_type const&>(*this);
    }
    operator id_type() const { return id(); }

    bool eoi() const {
        return static_cast<base_type const &>(*this).is_eoi();
    }

    // returns the Qi token value (get_value() supplies the Wave value)
    token_value_type value() const {
        return std::pair<string_type const &, position_type const &>(
            get_value(), static_cast<base_type const *>(this)->get_position());
    }

    // Wave requirements delegated to base class

    bool operator==(qi_token const & other) const {
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
    operator<< (std::ostream &os, qi_token<PositionT> const & tok) {
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
token_is_valid(qi_token<Position> const & t)
{
    return t.is_valid();
}

//
// Spirit.Qi customization points
//

namespace boost { namespace spirit { namespace traits
{

//
// Teach Spirit how to get data from our token into attributes
//

// generally following Spirit.Lex's lexertl/token.hpp here

// string or range requests the underlying char data
template<typename PositionT, typename StringT>
struct assign_to_attribute_from_value<StringT, qi_token<PositionT> >
{
    static void
    call(qi_token<PositionT> const & tok, StringT & attr)
    {
        // use the Wave accessor to get the string data
        attr = StringT(boost::begin(tok.value().first),
                       boost::end(tok.value().first));

    }
};
template<typename PositionT, typename StringT>
struct assign_to_container_from_value<StringT, qi_token<PositionT> >
    : assign_to_attribute_from_value<StringT, qi_token<PositionT> >
{};

// if the user wants position data instead
template<typename PositionT>
struct assign_to_attribute_from_value<PositionT, qi_token<PositionT> >
{
    static void
    call(qi_token<PositionT> const & tok, PositionT & attr)
    {
        attr = tok.value().second;
    }
};
// we don't support assigning positions to "containers"

// if the user wants both position and string value
template<typename PositionT, typename StringT>
struct assign_to_attribute_from_value<
    std::pair<StringT, PositionT>, qi_token<PositionT> >
{
    static void
    call(qi_token<PositionT> const & tok, std::pair<StringT, PositionT> & attr)
    {
        // delegate to existing handlers
        assign_to_attribute_from_value<StringT, qi_token<PositionT> >::call(tok, attr.first);
        assign_to_attribute_from_value<PositionT, qi_token<PositionT> >::call(tok, attr.second);
    }
};

// Support debug output
template <typename PositionT>
struct token_printer_debug<qi_token<PositionT> >
{
    typedef qi_token<PositionT> token_type;

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
struct qi_lex_iterator : boost::wave::cpplexer::lex_iterator<TokenT>
{
    using base_type = boost::wave::cpplexer::lex_iterator<TokenT>;
    using position_type = typename TokenT::position_type;

    // add the typedef that qi::token requires
    using base_iterator_type = typename TokenT::string_type::const_iterator;

    // forward constructors
    qi_lex_iterator() {}
    template<typename IteratorT>
    qi_lex_iterator(IteratorT beg, IteratorT end, position_type pos,
                    boost::wave::language_support lang)
        : base_type(beg, end, pos, lang) {}

};

