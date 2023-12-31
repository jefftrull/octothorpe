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
#include <fstream>
#include <optional>

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/FileManager.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"
#include "clang/Rewrite/Core/Rewriter.h"

#include <boost/iterator/function_output_iterator.hpp>

std::string get_source_range(clang::SourceManager const* sm,
                             clang::LangOptions lopt, clang::SourceRange range) {
    auto beg = range.getBegin();
    auto end = range.getEnd();
    clang::SourceLocation true_end =
        clang::Lexer::getLocForEndOfToken(end, 0, *sm, lopt);
    return std::string(sm->getCharacterData(beg),
                       sm->getCharacterData(true_end) - sm->getCharacterData(beg));
}

void print_source_range(std::ostream& os, clang::SourceManager const* sm,
                        clang::LangOptions lopt, clang::SourceRange range) {
    os << get_source_range(sm, lopt, range);
}

void print_source_range_info(std::ostream& os, clang::SourceManager const* sm,
                             clang::SourceRange range) {
    auto beg = range.getBegin();
    auto end = range.getEnd();
    os << "from line " << sm->getExpansionLineNumber(beg);
    os << " column " << sm->getExpansionColumnNumber(beg);
    os << " to line " << sm->getExpansionLineNumber(end);
    os << " column " << sm->getExpansionColumnNumber(end) << ":\n";
}

void print_decorated_source_range(std::ostream& os, clang::SourceManager const* sm,
                                  clang::LangOptions lopt, clang::SourceRange range) {
    print_source_range_info(os, sm, range);
    os << "===========\n";
    print_source_range(os, sm, lopt, range);
    os << "\n===========\n";
}

template<bool Sense>    // whether to find ranges where the symbols is defined
struct PPActions : clang::PPCallbacks
{
    PPActions(clang::LangOptions lopt,
              clang::SourceManager & sm,
              std::string mname,
              std::vector<clang::SourceRange>& source_ranges,
              std::vector<clang::SourceRange>& source_ranges_pp)
        : lopt_(lopt), sm_(sm), mname_(mname),
          source_ranges_(source_ranges), source_ranges_pp_(source_ranges_pp) {}

    void Ifdef(clang::SourceLocation loc,
               clang::Token const& tok,
               clang::MacroDefinition const&) override {
        // check for our target macro and sense
        if (tok.getIdentifierInfo()->getName().str() == mname_) {
            // determine where the #ifdef macro ends
            auto tok_end = clang::Lexer::getLocForEndOfToken(tok.getLocation(),
                                                             0, sm_, lopt_);
            cond_starts_.emplace(loc, std::make_pair(true, tok_end));
            else_loc_ = std::nullopt;
        }
    }

    void Ifndef(clang::SourceLocation loc,
                clang::Token const& tok,
                clang::MacroDefinition const&) override {
        if (tok.getIdentifierInfo()->getName().str() == mname_) {
            auto tok_end = clang::Lexer::getLocForEndOfToken(tok.getLocation(),
                                                             0, sm_, lopt_);
            cond_starts_.emplace(loc, std::make_pair(false, tok_end));
            else_loc_ = std::nullopt;
        }
    }

    // else and endif are reported as long as their corresponding if is not *within* a skipped region
    // Note in this area that source ranges are inclusive of their bounds, and the "end" location
    // may point to the start of a token, in which case the entire token is included.

    void Else(clang::SourceLocation elseloc,
              clang::SourceLocation ifloc) override {
        // see if this else is related to an ifdef/ifndef for our target macro
        auto start_it = cond_starts_.find(ifloc);
        if (start_it != cond_starts_.end()) {
            else_loc_ = clang::Lexer::getLocForEndOfToken(elseloc, 0, sm_, lopt_);
            if (start_it->second.first == Sense) {
                // this is the *end* of our range of interest
                // PP-inclusive range starts at hash, ends at trailing "e" of "else"
                source_ranges_pp_.emplace_back(ifloc.getLocWithOffset(-1),
                                               *else_loc_);
                // for PP-exclusive we use just past the end of the #ifdef/ifndef
                // which we stored when we found the statement
                source_ranges_.emplace_back(start_it->second.second,
                                            elseloc.getLocWithOffset(-2));  // *before* the hash
            }
            // otherwise this begins a range of interest which starts *after* the else
        }
    }        

    void Endif(clang::SourceLocation endifloc,
               clang::SourceLocation ifloc) override {
        // is this endif related to an ifdef/ifndef of interest?
        auto start_it = cond_starts_.find(ifloc);
        if (start_it != cond_starts_.end()) {
            auto end_of_endif = clang::Lexer::getLocForEndOfToken(endifloc, 0, sm_, lopt_);
            // this endif may terminate:
            // - an if of the desired sense without an else (range is ifloc through here)
            if ((start_it->second.first == Sense) && !else_loc_) {
                source_ranges_.emplace_back(start_it->second.second,
                                            endifloc.getLocWithOffset(-2));
                source_ranges_pp_.emplace_back(ifloc.getLocWithOffset(-1), end_of_endif);
            // - an if of the inverted sense with an else (range is else through here)
            } else if ((start_it->second.first != Sense) && else_loc_) {
                // else_loc_ is always "end of the else"
                // we use it for both purposes, assigning the #else always to the first
                // section for cleanup purposes
                source_ranges_.emplace_back(*else_loc_,
                                            endifloc.getLocWithOffset(-2));
                source_ranges_pp_.emplace_back(*else_loc_, end_of_endif);
            // - an if of inverted sense without an else - empty range
            } else if (start_it->second.first != Sense) {
                // an empty range must have end before start... but some parts of Clang don't like
                // we will detect this case before passing it on to any part of Clang
                source_ranges_.emplace_back(clang::SourceRange());
                source_ranges_pp_.emplace_back(clang::SourceRange());
            }
            // - an if of desired sense with else (we found the range when we found the else)
        }
    }        

private:
    clang::LangOptions          lopt_;
    clang::SourceManager const& sm_;
    std::string                 mname_;
    std::map<clang::SourceLocation,       // for remembering conditionals we later terminate
             std::pair<
                 bool,                    // "true" for ifdef, "false" for ifndef
                 clang::SourceLocation> > // where the if ends (last char of macro name)
        cond_starts_;

    std::optional<clang::SourceLocation> else_loc_;    // most recent "else", if any
    std::vector<clang::SourceRange>& source_ranges_;
    std::vector<clang::SourceRange>& source_ranges_pp_;

};

template<typename Node>
using RangeNodes = std::vector<std::vector<Node const *>>;

// We define our own type of "location" to be independent of any SourceManager
// It's capable of being turned into a Replacement
struct CondLocation
{
    CondLocation(clang::SourceManager const& sm,
                 clang::SourceLocation const& loc)
        : filename_(sm.getFilename(loc)), offset_(sm.getFileOffset(loc)) {}

    // so we can use in ordered containers
    bool operator<(const CondLocation& other) const {
        assert(other.filename_ == filename_);
        return (offset_ < other.offset_);
    }

    std::string const& getFilename() const {
        return filename_;
    }
    unsigned getFileOffset() const {
        return offset_;
    }

private:
    std::string filename_;
    unsigned    offset_;
};

struct CondRange {
    CondRange(clang::SourceManager const& sm,
              clang::SourceRange const& range)
        : beg_(CondLocation(sm, range.getBegin())),
          end_(CondLocation(sm, range.getEnd())) {}

    CondLocation const& getBegin() const {
        return beg_;
    }

    CondLocation const& getEnd() const {
        return end_;
    }

private:
    CondLocation beg_, end_;
};

// a class representing a conditional region in the form of two enclosing regions
// one which includes the preprocessor directives and which which doesn't
struct CondRegion {

    CondRegion(CondRange const& contents, CondRange const& contents_incl_pp)
        : contents_(contents), contents_incl_pp_(contents_incl_pp) {}

    CondRange const& contents() const {
        return contents_;
    }

    CondRange const& contents_with_pp() const {
        return contents_incl_pp_;
    }

private:
    CondRange contents_;         // between #ifdef/#ifndef/#else and #else/#endif
    CondRange contents_incl_pp_; // including the enclosing directives (for cleanup) 
};

struct RegionStatementProperties {
    std::size_t count;           // the number of statements found within the region
};

template<bool Sense>
struct SourceFileHooks : clang::tooling::SourceFileCallbacks
{
    SourceFileHooks(std::string mname,
                    std::vector<clang::SourceRange>& source_ranges,
                    std::vector<clang::SourceRange>& source_ranges_pp,
                    std::vector<std::optional<CondRegion>>& cond_regions,
                    RangeNodes<clang::Decl> const& decls,
                    RangeNodes<clang::Stmt> const& stmts,
                    std::vector<std::vector<std::string>>& type_names,
                    std::vector<RegionStatementProperties>& stmt_props,
                    clang::tooling::Replacements* replace,
                    std::string& preamble)
        : mname_(mname), source_ranges_(source_ranges), source_ranges_pp_(source_ranges_pp),
          cond_regions_(cond_regions), ci_(nullptr), decls_(decls), stmts_(stmts),
          type_names_(type_names), stmt_props_(stmt_props), replace_(replace), preamble_(preamble) {}

    ~SourceFileHooks() override {}

    bool handleBeginSource(clang::CompilerInstance & ci) override {
        ci_ = &ci;
        // at this point the preprocessor has been initialized, so we cannot add definitions
        // we can, however, set up callbacks
        ci.getPreprocessor().addPPCallbacks(
            std::make_unique<PPActions<Sense>>(ci.getLangOpts(), ci.getSourceManager(),
                                                mname_, source_ranges_, source_ranges_pp_));
        // when the preprocessor runs it will update source_ranges as it finds conditionals
        return true;
    }

    void handleEndSource() override {
        // return information about the source ranges we found and their contents
        // it seems that by the time the RefactoringTool finishes running some of the
        // compiler/ast information gets lost, so we do it here while we can still do lookups
        using namespace clang;
        SourceManager const* sm = &ci_->getSourceManager();
        LangOptions   lopt = ci_->getLangOpts();

        // fill CondRegion container with default-constructed (therefore empty) ranges
        cond_regions_.resize(source_ranges_.size());

        for ( std::size_t i = 0; i < source_ranges_.size(); ++i) {
            if (source_ranges_[i].isInvalid()) {
                // this means an empty range.  We leave a placeholder here to sync
                // up the indices between senses.
                continue;
            }
            cond_regions_[i] = CondRegion(CondRange(*sm, source_ranges_[i]),
                                          CondRange(*sm, source_ranges_pp_[i]));
            std::cout << "The range ";
            print_decorated_source_range(std::cout, sm, lopt, source_ranges_[i]);
            if (source_ranges_[i].getBegin() == source_ranges_[i].getEnd()) {
                std::cout << " is empty\n";
                continue;
            }
            if (decls_[i].empty() && stmts_[i].empty()) {
                std::cout << " contains nothing we are interested in\n";
            }
            if (!stmts_[i].empty()) {
                std::cout << " contains " << stmts_[i].size() << " statements:\n";
                for( Stmt const * stmt : stmts_[i] ) {
                    print_source_range(std::cout, sm, lopt, stmt->getSourceRange());
                    std::cout << ";\n";
                }
            } else if (!decls_[i].empty()) {
                std::cout << " contains declarations, but no statements\n";
            }

            // create a replacement that removes this conditional range (including PP directives)
            if (replace_->add(tooling::Replacement(*sm, CharSourceRange(source_ranges_pp_[i], true),
                                                   "", lopt))) {
                throw std::logic_error("unable to create Replacement to remove conditional range");
            }
        }

        // post-process bits of the AST we gathered to produce refactoring info that persists
        // after this tool completes
        type_names_.resize(decls_.size());
        for (std::size_t i = 0; i < decls_.size(); ++i) {
            for (auto decl : decls_[i]) {
                if (clang::TypedefDecl const* td = llvm::dyn_cast<clang::TypedefDecl>(decl)) {
                    type_names_[i].emplace_back(td->getName());
                } else if (auto ud = llvm::dyn_cast<clang::UsingDecl>(decl)) {
                    type_names_[i].emplace_back(ud->getName());
                }
                // there should be no other types, actually, as we restrict to the
                // above two in the Matcher
            }
        }

        // figure out how many statements there are in each region
        // we won't add closures around code without statements
        stmt_props_.resize(stmts_.size());
        for (std::size_t i = 0; i < stmts_.size(); ++i) {
            stmt_props_[i].count = stmts_[i].size();
            // this is where we can record the statement text
        }

        // create a specialization for this sense of the target macro
        std::string cond_class;
        if (Sense) {
            // base template is the "true" case
            // Leveraging the fact that we run the "true" case first...
            cond_class += std::string("template<bool MacroDefined>\nstruct ");
            cond_class += (mname_ + "_class {\n");
        } else {
            cond_class = std::string("template<>\nstruct ");
            cond_class += (mname_ + "_class<false" + "> {\n");
        }
        for ( auto const& declgroup : decls_ ) {
            for ( auto decl : declgroup ) {
                cond_class += "    ";
                cond_class += get_source_range(&decl->getASTContext().getSourceManager(),
                                               decl->getASTContext().getLangOpts(),
                                               decl->getSourceRange());
                cond_class += ";\n";
            }
        }
        cond_class += "};\n";
        preamble_ += cond_class;

    }

private:
    std::string mname_;
    std::vector<clang::SourceRange>& source_ranges_, source_ranges_pp_;
    std::vector<std::optional<CondRegion>>& cond_regions_;
    clang::CompilerInstance* ci_;
    RangeNodes<clang::Decl> const & decls_;
    RangeNodes<clang::Stmt> const & stmts_;
    std::vector<std::vector<std::string>>& type_names_;
    std::vector<RegionStatementProperties>& stmt_props_;
    clang::tooling::Replacements * replace_;
    std::string&                   preamble_;

};

namespace custom_matchers {

// define an AST matcher for a source location range
// it will match all statements whose associated start/end locations are within the range
AST_MATCHER_P(clang::Stmt,                statementInRange,
              clang::SourceRange,         range) {
    // true if the statement node is entirely within the supplied range
    // i.e. they can be coterminous but the statement cannot start before or end after
    clang::SourceManager const& sm = Finder->getASTContext().getSourceManager();
    return !sm.isBeforeInTranslationUnit(Node.getBeginLoc(), range.getBegin()) &&
        !sm.isBeforeInTranslationUnit(range.getEnd(), Node.getEndLoc());
}

AST_MATCHER_P(clang::Decl,                declInRange,
              clang::SourceRange,         range) {
    clang::SourceManager const& sm = Finder->getASTContext().getSourceManager();
    return !sm.isBeforeInTranslationUnit(Node.getBeginLoc(), range.getBegin()) &&
        !sm.isBeforeInTranslationUnit(range.getEnd(), Node.getEndLoc());
}

// BOZO can we do the above polymorphically in the node type (decl/stmt)?

}

// action for when we find a node within a source range
template<typename AstNode>
struct RangeMatchHandler : clang::ast_matchers::MatchFinder::MatchCallback {
    
    RangeMatchHandler(std::vector<AstNode const*>& nodes) : nodes_(nodes) {}

    virtual void run(clang::ast_matchers::MatchFinder::MatchResult const& result) {
        AstNode const * node = result.Nodes.getNodeAs<AstNode>("target");
        nodes_.push_back(node);
    }

private:
    std::vector<AstNode const*>& nodes_;       // a place to store nodes within our range
};

// Test hook to install matchers
// We don't know which source ranges we want to find until preprocessing completes,
// which means we have to set up matchers after parsing begins but before AST traversal
// it's a little weird to use this test hook but it's exactly what we need
struct MatcherInstaller :  clang::ast_matchers::MatchFinder::ParsingDoneTestCallback {

    ~MatcherInstaller() override {}

    MatcherInstaller(clang::ast_matchers::MatchFinder& finder,
                     std::vector<clang::SourceRange> const& ranges,
                     RangeNodes<clang::Decl>& decl_nodes,
                     RangeNodes<clang::Stmt>& stmt_nodes,
                     std::vector<std::vector<std::string>>& type_names)
        : finder_(finder), ranges_(ranges),
          decl_nodes_(decl_nodes), stmt_nodes_(stmt_nodes), type_names_(type_names) {}

    virtual void run() override {
        // install matchers for the given ranges into the finder
        using namespace clang::ast_matchers;
        using namespace custom_matchers;
        
        // ensure handler vectors don't resize, invalidating pointers
        decl_handlers_.reserve(ranges_.size());
        stmt_handlers_.reserve(ranges_.size());
        decl_nodes_.reserve(ranges_.size());
        stmt_nodes_.reserve(ranges_.size());

        for( auto const& range : ranges_ ) {
            // typedef matcher
            decl_nodes_.emplace_back();
            type_names_.emplace_back();
            decl_handlers_.emplace_back(decl_nodes_.back());
            // statement matcher
            stmt_nodes_.emplace_back();
            stmt_handlers_.emplace_back(stmt_nodes_.back());

            if (range.isInvalid()) {
                // one of our empty ranges.  Do not install finder/matcher
                // but keep placeholders so ranges line up between defined/undefined conditions
                continue;
            }

            // install range finder for conditional declarations
            finder_.addMatcher(
                decl(
                    isExpansionInMainFile(),   // not in an included header
                    declInRange(range),        // within target range
                    anyOf(typedefDecl(), usingDecl()),  // a type declaration
                    decl().bind("target")),
                &decl_handlers_.back());

            // install range finder for conditional statements
            finder_.addMatcher(
                stmt(                          // statement requirements:
                    isExpansionInMainFile(),
                    statementInRange(range),
                    hasParent(
                        compoundStmt()),       // part of compound statement
                    unless(declStmt(           // not a type declaration
                               hasSingleDecl(
                                   anyOf(typedefDecl(), usingDecl())))),
                    stmt().bind("target")),       // remember it
                &stmt_handlers_.back());
        }
    }

private:
    clang::ast_matchers::MatchFinder&      finder_;
    std::vector<clang::SourceRange> const& ranges_;

    template<typename Node>
    using HandlerVec = std::vector<RangeMatchHandler<Node>>;
    HandlerVec<clang::Decl>                decl_handlers_;
    HandlerVec<clang::Stmt>                stmt_handlers_;
    RangeNodes<clang::Decl>&               decl_nodes_;
    RangeNodes<clang::Stmt>&               stmt_nodes_;
    // names of the types defined in each range
    // for "using" statement
    std::vector<std::vector<std::string>>& type_names_;
};

// run a tool (usually a Finder) on an input file
// Make the supplied macro be defined on the command line if Sense is true
// optionally add source file callbacks to hook the beginning and end of each file processed
template<bool Sense, typename FactoryT>
int runToolOnFile(FactoryT*                            consumerFactory,
                  std::string                          mname,
                  std::string                          fileName,
                  clang::tooling::SourceFileCallbacks* cb = nullptr) {
    using namespace clang::tooling;
    // create a fake command line of type Clang tools accept
    std::vector<char const*> args;
    args.push_back("c2p");
    args.push_back(fileName.c_str());
    // append -D for the "macro defined" case
    args.push_back("--");
    args.push_back("-std=c++14");
    if (Sense) {
        std::string define_macro("-D");
        define_macro += mname;
        args.push_back(define_macro.c_str());
    }
    // prepare tool arguments
    // avoiding the use of CommonOptionsParser, which uses statics...
    int args_c = args.size();
    std::string error_msg;
    std::unique_ptr<FixedCompilationDatabase>
        compdb(FixedCompilationDatabase::loadFromCommandLine(args_c, args.data(), error_msg));
    std::vector<std::string> comp_file_list(1, fileName);

    // define the tool from those options
    RefactoringTool     tool(*compdb, llvm::ArrayRef<std::string>(comp_file_list));

    return tool.run(newFrontendActionFactory(consumerFactory, cb).get());    
}

template<bool Sense, typename FactoryT>
int runToolOnString(FactoryT*                            consumerFactory,
                    std::string                          mname,
                    std::string                          contents,
                    clang::tooling::SourceFileCallbacks* cb = nullptr) {
    using namespace clang::tooling;
    // create a fake command line of type Clang tools accept
    std::vector<std::string> args;
    // append -D for the "macro defined" case
    args.push_back("-std=c++14");
    if (Sense) {
        std::string define_macro("-D");
        define_macro += mname;
        args.push_back(define_macro.c_str());
    }

    int result = runToolOnCodeWithArgs(newFrontendActionFactory(consumerFactory, cb)->create(),
                                       contents, args);
    return result;
}

template<bool Sense>
int FindConditionalNodes(std::string                                           mname,
                         std::string                                           fileName,
                         // result storage
                         std::vector<std::optional<CondRegion>>& cond_regions,
                         std::vector<std::set<std::string>>&                   typedefs,
                         std::vector<RegionStatementProperties>&               stmt_props,
                         clang::tooling::Replacements&                         replacements,
                         std::string&                                          preamble)
{
    using namespace clang;
    using namespace clang::tooling;
    using namespace clang::ast_matchers;

    // strictly for communication between match callbacks and the source file hooks
    // which are defined in this scope.  This data becomes invalid after the tool is run:
    std::vector<SourceRange>         source_ranges, source_ranges_pp;
    RangeNodes<Decl>                 decls;
    RangeNodes<Stmt>                 stmts;

    // non-Clang stuff can and will outlive the tool though:
    std::vector<std::vector<std::string>>
                                     type_names;   // types defined in each range

    // create callbacks for storing the conditional ranges as the preprocessor finds them
    SourceFileHooks<Sense>           source_hooks(mname, source_ranges, source_ranges_pp,
                                                  cond_regions, decls, stmts,
                                                  type_names, stmt_props,
                                                  &replacements, preamble);

    // use test hook to set up range matchers: after preprocessing, but before AST visitation
    MatchFinder           finder;
    MatcherInstaller      set_up_source_ranges(finder, source_ranges, decls, stmts, type_names);
    finder.registerTestCallbackAfterParsing(&set_up_source_ranges);


    std::cout << "Conditional source ranges for when FOO is ";
    std::cout << (Sense ? "defined" : "not defined") << ":\n";
    // run the tool
    if (int result = runToolOnFile<Sense>(&finder, mname, fileName, &source_hooks)) {
        return result;
    }

    if (!Sense) {
        // choose a specialization
        std::string choose_condition("#ifdef ");
        choose_condition += (mname + "\n");
        choose_condition += ("    using " + mname + "_t = " + mname + "_class<true>;\n");
        choose_condition += "#else\n";
        choose_condition += ("    using " + mname + "_t = " + mname + "_class<false>;\n");
        choose_condition += "#endif\n";

        preamble += choose_condition;
    }

    // remember the types that were defined in this condition
    typedefs.resize(type_names.size());
    for( std::size_t i = 0; i < type_names.size(); ++i) {
        // uniquify by range via set insertion
        std::copy(type_names[i].begin(), type_names[i].end(),
                  std::inserter(typedefs[i], typedefs[i].end()));
    }

    return 0;
}

// a list of variable names and types found captured by a single lambda
struct capture_t {
    std::string varname;
    std::string vartype;
    bool        is_const;            // presently unimplemented/unused
};
using capture_list_t = std::vector<capture_t>;

// trick: instantiate one of these for each lambda we insert
// that way we don't have to deal with interpreting the lambda name
// callback will keep a reference to the statement region properties' capture list
struct CaptureReporter : clang::ast_matchers::MatchFinder::MatchCallback {
    CaptureReporter(capture_list_t& captures) : captures_(captures) {}
    virtual void run(clang::ast_matchers::MatchFinder::MatchResult const& result) override {
        using namespace clang;
        LambdaExpr const * lambda = result.Nodes.getNodeAs<LambdaExpr>("lambda");
        // record each of its captures
        for (clang::LambdaCapture const & lc : lambda->captures()) {
            if (lc.capturesVariable()) {
                capture_t capture;
                capture.varname = lc.getCapturedVar()->getQualifiedNameAsString();
                capture.vartype = lc.getCapturedVar()->getType().getAsString();
                std::cerr << "recording variable " << capture.varname << " type " << capture.vartype << "\n";
                captures_.push_back(capture);
            }
        }
    }
private:
    capture_list_t&  captures_;
};

// Edit text to surround conditional regions containing statements with a lambda capture
using cond_region_list_t = std::vector<std::optional<CondRegion>>;
std::string
annotate_conditionals_with_lambdas(std::string const& body,
                                   std::vector<RegionStatementProperties> const& stmt_props,
                                   cond_region_list_t const & cond_regions) {
    // create replacements list to add lambdas for this sense
    using namespace clang::tooling;
    Replacements replacements;
    std::size_t lambda_counter = 0;
    for (auto region : cond_regions) {
        // the region may be empty, which indicates that it wasn't present, i.e.
        // is the other sense of something that lacked an "else".  We want the indices
        // to stay in sync with the other sense, so:
        if (!region ||
            !stmt_props[lambda_counter].count) { // also: no statements inside this region
            lambda_counter++;
            continue;
        }

        std::string closure_name("_cond_statement_closure_");
        closure_name += std::to_string(lambda_counter++);
        std::string lambda_start = "\nauto " + closure_name + " = [&]() {\n";
        // a replacement to insert this at the beginning of the conditional region
        auto cond_range = region->contents();
        if (replacements.add(
                Replacement(cond_range.getBegin().getFilename(),
                            cond_range.getBegin().getFileOffset(),
                            0, lambda_start))) {
            throw std::logic_error("unable to create Replacement from lambda preamble");
        }
        // close the end
        std::string lambda_end("};\n");
        lambda_end += closure_name + "();\n";   // execute lambda to retain semantic equivalence
        if (replacements.add(
                Replacement(cond_range.getEnd().getFilename(),
                            cond_range.getEnd().getFileOffset() + 1,
                            0, lambda_end))) {
            throw std::logic_error("unable to create Replacement from lambda execution");
        }
    }

    // perform replacements on string
    auto result = applyAllReplacements(body, replacements);
    if (!result) {
        throw std::logic_error("unable to create Replacement from lambda execution");
    }
    return result.get();
}    

// take lambda-annotated code and produce a list of captures
template<bool Sense>
std::vector<capture_list_t>
analyze_captures(std::string                            const& annotated_code,
                 std::string                            const& mname,
                 std::vector<RegionStatementProperties> const& stmt_props,
                 cond_region_list_t                     const& cond_regions) {

    using namespace clang::tooling;
    using namespace clang::ast_matchers;

    std::vector<capture_list_t>     result(cond_regions.size());
    std::vector<DeclarationMatcher> matchers;
    std::vector<CaptureReporter>    reporters;

    // create a set of matchers for the generated closures, with related callbacks
    // to record each captured variable
    MatchFinder finder;
    for (std::size_t i = 0; i < cond_regions.size(); ++i) {
        matchers.emplace_back(
            varDecl(
                hasType(autoType()),
                matchesName("_cond_statement_closure_" + std::to_string(i)),
                hasInitializer(
                    cxxConstructExpr(
                        hasDescendant(    // BOZO prefer to use something more specific?
                            lambdaExpr().bind("lambda"))))));
        reporters.emplace_back(result[i]);

        if (!cond_regions[i] || !stmt_props[i].count) {
            // a nonexistent region or one with no statements
            continue;
        }
        // run matcher to map lambda names to capture list
        finder.addMatcher(matchers[i], &reporters[i]);
    }

    // run tool with matchers and callbacks to produce result
    runToolOnString<Sense>(&finder, mname, annotated_code);

    // return capture list
    return result;
}


// figure out the parameters of the static member function we will generate
// by running matchers etc.
template<bool Sense>
std::vector<capture_list_t>
vars_used(std::string const& mname,
          std::string filename,
          std::vector<RegionStatementProperties> const& stmt_props,
          cond_region_list_t const& cond_regions) {

    // get file into a string
    std::ifstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("could not open file " + filename);
    }
    file.unsetf(std::ios::skipws);
    std::string contents{std::istream_iterator<char>(file),
                         std::istream_iterator<char>()};

    // annotate file contents with lambdas surrounding conditionals containing statements
    std::string annotatedContents = annotate_conditionals_with_lambdas(contents, stmt_props, cond_regions);

    // Run capture analysis on the annotated contents to collect statements
    return analyze_captures<Sense>(annotatedContents, mname, stmt_props, cond_regions);
}

// actually generate a string containing the static member function
// to implement
template<bool Sense>
std::string
fn_wrap_statements(std::string statements,
                   std::string fn_name,   // also macro name? or class name?
                   capture_list_t const & params);


int main(int argc, char const **argv) {

    using namespace clang;

    if (argc != 3) {
        std::cerr << "usage: " << argv[0] << " MACRO filename\n";
        return 1;
    }
            
    /*
     * Evaluate macro defined condition
     */

    // when tool run completes we will have the following data:
    tooling::Replacements replacements;             // modification instructions
    std::string           preamble;                 // definitions inserted at top of file

    // build and run for "defined" case
    cond_region_list_t                     cond_regions_defined;   // source region for each ifdef
    std::vector<std::set<std::string>>     typedefs_defined;
    std::vector<RegionStatementProperties> stmt_props_defined;
    if (int result = FindConditionalNodes<true>(argv[1], argv[2], cond_regions_defined,
                                                typedefs_defined, stmt_props_defined,
                                                replacements, preamble)) {
        return result;
    }

    // and the same for the "undefined" case:
    cond_region_list_t cond_regions_undefined;
    std::vector<std::set<std::string>> typedefs_undefined;
    std::vector<RegionStatementProperties> stmt_props_undefined;
    if (int result = FindConditionalNodes<false>(argv[1], argv[2], cond_regions_undefined,
                                                 typedefs_undefined, stmt_props_undefined,
                                                 replacements, preamble)) {
        return result;
    }

    // analyze statements in each conditional region
    auto vars_defined = vars_used<true>(argv[1], argv[2], stmt_props_defined, cond_regions_defined);
    std::cout << "TRUE case:\n";
    for (std::size_t i = 0; i < vars_defined.size(); ++i) {
        if (cond_regions_defined[i] && stmt_props_defined[i].count) {
            std::cout << "capture expression " << i << " produced the following parameters:\n";
            for (auto capture: vars_defined[i]) {
                std::cout << capture.varname << " type " << capture.vartype << "\n";
            }
        }
    }

    auto vars_undefined = vars_used<false>(argv[1], argv[2], stmt_props_undefined, cond_regions_undefined);
    std::cout << "FALSE case:\n";
    for (std::size_t i = 0; i < vars_undefined.size(); ++i) {
        if (cond_regions_undefined[i] && stmt_props_undefined[i].count) {
            std::cout << "capture expression " << i << " produced the following parameters:\n";
            for (auto capture: vars_undefined[i]) {
                std::cout << capture.varname << " type " << capture.vartype << "\n";
            }
        }
    }

    // if any conditional regions have matching (in name) type declarations,
    // replace with a single one referring to the chosen specialization
    for (std::size_t i = 0; i < cond_regions_defined.size(); ++i) {
        if (!cond_regions_defined[i] || !cond_regions_undefined[i]) {
            continue;
        }
        // put using statement right before directive that starts the conditional region
        CondLocation start = std::min(cond_regions_defined[i]->contents_with_pp().getBegin(),
                                      cond_regions_undefined[i]->contents_with_pp().getBegin());
        std::string mname(argv[1]);
        std::set_intersection(
            typedefs_defined[i].begin(), typedefs_defined[i].end(),
            typedefs_undefined[i].begin(), typedefs_undefined[i].end(),
            // for each type declared in BOTH configurations:
            boost::make_function_output_iterator(
                [&](std::string const& t) {
                    // insert a using statement in the body:
                    std::string tdef("    using " + t + " = " + mname + "_t::" + t + ";\n");
                    if (replacements.add(
                            tooling::Replacement(start.getFilename(),
                                                 start.getFileOffset(),
                                                 0, tdef))) {
                        throw std::logic_error("unable to create Replacement from using statement for type");
                    };
                }));
    }    

    // finally add the class definition, specialization, and using statements
    if (replacements.add(
            tooling::Replacement(argv[2], 0, 0, preamble))) {
        throw std::logic_error("failed to insert preamble as a Replacement");
    }

    std::cerr << "replacements:\n";
    for ( auto const& rep : replacements ) {
        std::cerr << rep.toString() << "\n";
    }

    // apply all replacements to original source file
    // (code from RefactoringTool::runAndSave)
    IntrusiveRefCntPtr<DiagnosticOptions> diag_opts = new DiagnosticOptions();
    TextDiagnosticPrinter tdp(llvm::errs(), &*diag_opts);
    DiagnosticsEngine diagnostics(
        IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()),
        &*diag_opts, &tdp, false);
    FileManager fm{FileSystemOptions()};
    SourceManager sources(diagnostics, fm);

    LangOptions DefaultLangOptions;
    Rewriter rewriter(sources, DefaultLangOptions);
    if (!tooling::applyAllReplacements(replacements, rewriter)) {
        std::cerr << "rewriting of source file failed\n";
        return 1;
    }
    if (rewriter.overwriteChangedFiles()) {
        std::cerr << "failed to save results\n";
        return 2;
    }

    
    return 0;
}
