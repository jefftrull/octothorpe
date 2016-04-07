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
#include <experimental/optional>

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

// BOZO needs a better name
// BOZO remove unneeded sm and lopt members
template<bool Sense>    // whether to find ranges where the symbols is defined
struct MyCallbacks : clang::PPCallbacks
{
    MyCallbacks(clang::LangOptions lopt,
                clang::SourceManager & sm,
                std::string mname,
                std::vector<clang::SourceRange>& cond_ranges)
        : lopt_(lopt), sm_(sm), mname_(mname), cond_ranges_(cond_ranges) {}

    void Ifdef(clang::SourceLocation loc,
               clang::Token const& tok,
               clang::MacroDefinition const& md) override {
        // check for our target macro and sense
        if (tok.getIdentifierInfo()->getName().str() == mname_) {
            cond_starts_.emplace(loc, true);
            else_loc_ = std::experimental::nullopt;
        }
    }

    void Ifndef(clang::SourceLocation loc,
                clang::Token const& tok,
                clang::MacroDefinition const& md) override {
        if (tok.getIdentifierInfo()->getName().str() == mname_) {
            cond_starts_.emplace(loc, false);
            else_loc_ = std::experimental::nullopt;
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
            if (start_it->second == Sense) {
                // this is the *end* of our range of interest
                cond_ranges_.emplace_back(ifloc.getLocWithOffset(-1),
                                          elseloc.getLocWithOffset(-2));  // *before* the hash
            }
            else_loc_ = elseloc;
        }
    }        

    void Endif(clang::SourceLocation endifloc,
               clang::SourceLocation ifloc) override {
        // is this endif related to an ifdef/ifndef of interest?
        auto start_it = cond_starts_.find(ifloc);
        if (start_it != cond_starts_.end()) {
            // this endif may terminate:
            // - an if of the desired sense without an else (range is ifloc through here)
            if ((start_it->second == Sense) && !else_loc_) {
                cond_ranges_.emplace_back(ifloc.getLocWithOffset(-1), endifloc);
            // - an if of the inverted sense with an else (range is else through here)
            } else if ((start_it->second != Sense) && else_loc_) {
                cond_ranges_.emplace_back(else_loc_->getLocWithOffset(-1), endifloc);
            // - an if of inverted sense without an else - empty range
            } else if (start_it->second != Sense) {
                // an empty range must have end before start... but some parts of Clang don't like
                // we will detect this case before passing it on to any part of Clang
                cond_ranges_.emplace_back(clang::SourceRange());
            }
            // - an if of desired sense with else (we found the range when we found the else)
        }
    }        

private:
    clang::LangOptions    lopt_;
    clang::SourceManager& sm_;
    std::string           mname_;
    std::map<clang::SourceLocation, bool> cond_starts_;
    std::experimental::optional<clang::SourceLocation> else_loc_;    // most recent "else", if any
    std::vector<clang::SourceRange>& cond_ranges_;

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


template<bool Sense>
struct PPCallbacksInstaller : clang::tooling::SourceFileCallbacks
{
    PPCallbacksInstaller(std::string mname,
                         std::vector<clang::SourceRange>& source_ranges,
                         std::vector<std::experimental::optional<CondRange>>& cond_ranges,
                         RangeNodes<clang::Decl> const& decls,
                         RangeNodes<clang::Stmt> const& stmts,
                         clang::tooling::Replacements* replace)
        : mname_(mname), source_ranges_(source_ranges), cond_ranges_(cond_ranges),
          ci_(nullptr), decls_(decls), stmts_(stmts), replace_(replace) {}

    ~PPCallbacksInstaller() override {}

    bool handleBeginSource(clang::CompilerInstance & ci, StringRef fn) override {
        ci_ = &ci;
        fn_ = fn;
        // at this point the preprocessor has been initialized, so we cannot add definitions
        // we can, however, set up callbacks
        ci.getPreprocessor().addPPCallbacks(
            llvm::make_unique<MyCallbacks<Sense>>(ci.getLangOpts(), ci.getSourceManager(),
                                                  mname_, source_ranges_));
        return true;
    }

    void handleEndSource() override {
        // return information about the source ranges we found and their contents
        // it seems that by the time the RefactoringTool finishes running some of the
        // compiler/ast information gets lost, so we do it here while we can still do lookups
        using namespace clang;
        SourceManager const* sm = &ci_->getSourceManager();
        LangOptions   lopt = ci_->getLangOpts();

        // fill CondRange container with default-constructed (therefore empty) ranges
        cond_ranges_.resize(source_ranges_.size());

        for ( std::size_t i = 0; i < source_ranges_.size(); ++i) {
            if (source_ranges_[i].isInvalid()) {
                continue;
            }
            cond_ranges_[i] = CondRange(*sm, source_ranges_[i]);
            std::cout << "The range ";
            print_source_range_info(std::cout, sm, source_ranges_[i]);
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
            }
            // create a replacement that removes this conditional range
            replace_->insert(tooling::Replacement(*sm, CharSourceRange(source_ranges_[i], true),
                                                  "", lopt));

        }

        // create a specialization for this sense of the target macro
        std::string cond_class("template<>\nstruct ");
        cond_class += (mname_ + "_class<" + (Sense ? "true" : "false") + "> {\n");
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

        // create a Replacement from it
        replace_->insert(tooling::Replacement(fn_, 0, 0, cond_class));  // insert at beginning

    }

private:
    std::string mname_;
    std::vector<clang::SourceRange>& source_ranges_;
    std::vector<std::experimental::optional<CondRange>>& cond_ranges_;
    clang::CompilerInstance* ci_;
    RangeNodes<clang::Decl> const & decls_;
    RangeNodes<clang::Stmt> const & stmts_;
    clang::tooling::Replacements * replace_;

    StringRef fn_;
};

namespace custom_matchers {

// define an AST matcher for a source location range
// it will match all statements whose associated start/end locations are within the range
AST_MATCHER_P(clang::Stmt,                statementInRange,
              clang::SourceRange,         range) {
    // true if the statement node is entirely within the supplied range
    // i.e. they can be coterminous but the statement cannot start before or end after
    clang::SourceManager const& sm = Finder->getASTContext().getSourceManager();
    return !sm.isBeforeInTranslationUnit(Node.getLocStart(), range.getBegin()) &&
        !sm.isBeforeInTranslationUnit(range.getEnd(), Node.getLocEnd());
}

AST_MATCHER_P(clang::Decl,                declInRange,
              clang::SourceRange,         range) {
    clang::SourceManager const& sm = Finder->getASTContext().getSourceManager();
    return !sm.isBeforeInTranslationUnit(Node.getLocStart(), range.getBegin()) &&
        !sm.isBeforeInTranslationUnit(range.getEnd(), Node.getLocEnd());
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
                     RangeNodes<clang::Stmt>& stmt_nodes)
        : finder_(finder), ranges_(ranges), decl_nodes_(decl_nodes), stmt_nodes_(stmt_nodes) {}

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
};

template<bool Sense>
int FindConditionalNodes(char const ** argv,
                         // result storage
                         std::vector<std::experimental::optional<CondRange>>& cond_ranges,
                         std::vector<std::set<std::string>>& typedefs,
                         clang::tooling::Replacements&    replacements)
{
    using namespace clang;
    using namespace clang::tooling;
    using namespace clang::ast_matchers;

    // create a fake command line of type Clang tools accept
    std::vector<char const*> args;
    args.push_back(argv[0]);
    args.push_back(argv[2]);
    args.push_back("--");
    // append -D for the "macro defined" case
    std::string mname(argv[1]);
    std::string define_macro("-D");
    if (Sense) {
        define_macro += mname;
        args.push_back(define_macro.c_str());
    }
    int args_c = args.size();
    // prepare tool arguments
    // avoiding the use of CommonOptionsParser, which uses statics...
    std::unique_ptr<FixedCompilationDatabase>
        compdb(FixedCompilationDatabase::loadFromCommandLine(args_c, args.data()));
    std::vector<std::string> comp_file_list(1, argv[2]);
    // define the tool from those options
    RefactoringTool     tool(*compdb, comp_file_list);

    std::vector<SourceRange>         source_ranges;
    RangeNodes<Decl>                 decls;
    RangeNodes<Stmt>                 stmts;

    // create callbacks for storing the conditional ranges as the preprocessor finds them
    PPCallbacksInstaller<Sense>      ppci(mname, source_ranges, cond_ranges,
                                          decls, stmts, &replacements);

    // use test hook to set up range matchers: after preprocessing, but before AST visitation
    MatchFinder           finder;
    MatcherInstaller      set_up_source_ranges(finder, source_ranges, decls, stmts);
    finder.registerTestCallbackAfterParsing(&set_up_source_ranges);

    if (Sense) {
        // seed replacements with the base template
        // using the fact that we run the "true" case first...
        std::string base_class("template<bool MacroDefined>\nstruct ");
        base_class += (mname + "_class;\n");
        replacements.insert(Replacement(comp_file_list[0], 0, 0, base_class));
    }

    // run the tool

    std::cout << "Conditional source ranges for when FOO is ";
    std::cout << (Sense ? "defined" : "not defined") << ":\n";
    if (int result = tool.run(newFrontendActionFactory(&finder, &ppci).get())) {
        return result;
    }


    return 0;
}

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

    // build and run for "defined" case
    std::vector<std::experimental::optional<CondRange>> cond_ranges_defined;   // source range for each ifdef
    std::vector<std::set<std::string>> typedefs_defined;
    if (int result = FindConditionalNodes<true>(argv, cond_ranges_defined, typedefs_defined, replacements)) {
        return result;
    }

    // and the same for the "undefined" case:
    std::vector<std::experimental::optional<CondRange>> cond_ranges_undefined;
    std::vector<std::set<std::string>> typedefs_undefined;
    if (int result = FindConditionalNodes<false>(argv, cond_ranges_undefined, typedefs_undefined, replacements)) {
        return result;
    }

    std::cerr << "replacements:\n";
    for ( auto const& rep : replacements ) {
        std::cerr << rep.toString() << "\n";
    }

    // apply all replacements to original source file
    // (code from RefactoringTool::runAndSave)
    LangOptions DefaultLangOptions;
    IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts = new DiagnosticOptions();
    TextDiagnosticPrinter tdp(llvm::errs(), &*DiagOpts);
    DiagnosticsEngine diagnostics(
        IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()),
        &*DiagOpts, &tdp, false);
    FileManager fm{FileSystemOptions()};
    SourceManager sources(diagnostics, fm);
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
