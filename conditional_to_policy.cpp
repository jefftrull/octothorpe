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
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Frontend/CompilerInstance.h"

static llvm::cl::OptionCategory ToolingSampleCategory("Ifdef converter");

void print_source_range(std::ostream& os, clang::SourceManager const* sm,
                        clang::LangOptions lopt, clang::SourceRange range) {
    auto beg = range.getBegin();
    auto end = range.getEnd();
    clang::SourceLocation true_end =
        clang::Lexer::getLocForEndOfToken(end, 0, *sm, lopt);
    os << std::string(sm->getCharacterData(beg),
                      sm->getCharacterData(true_end) - sm->getCharacterData(beg));
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

    void Else(clang::SourceLocation elseloc,
              clang::SourceLocation ifloc) override {
        // see if this else is related to an ifdef/ifndef for our target macro
        auto start_it = cond_starts_.find(ifloc);
        if (start_it != cond_starts_.end()) {
            if (start_it->second == Sense) {
                // this is the *end* of our range of interest
                cond_ranges_.emplace_back(ifloc, elseloc);
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
                cond_ranges_.emplace_back(ifloc, endifloc);
            // - an if of the inverted sense with an else (range is else through here)
            } else if ((start_it->second != Sense) && else_loc_) {
                cond_ranges_.emplace_back(*else_loc_, endifloc);
            // - an if of inverted sense without an else - empty range
            } else if (start_it->second != Sense) {
                cond_ranges_.emplace_back(endifloc, endifloc);
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

template<bool Sense>
struct PPCallbacksInstaller : clang::tooling::SourceFileCallbacks
{
    PPCallbacksInstaller(std::string mname,
                         std::vector<clang::SourceRange>& cond_ranges,
                         RangeNodes<clang::Decl> const& decls,
                         RangeNodes<clang::Stmt> const& stmts)
        : mname_(mname), cond_ranges_(cond_ranges), ci_(nullptr),
          decls_(decls), stmts_(stmts) {}

    ~PPCallbacksInstaller() override {}

    bool handleBeginSource(clang::CompilerInstance & ci, StringRef fn) override {
        ci_ = &ci;
        // at this point the preprocessor has been initialized, so we cannot add definitions
        // we can, however, set up callbacks
        ci.getPreprocessor().addPPCallbacks(
            llvm::make_unique<MyCallbacks<Sense>>(ci.getLangOpts(), ci.getSourceManager(),
                                                  mname_, cond_ranges_));
        return true;
    }

    void handleEndSource() override {
        // return information about the source ranges we found and their contents
        // it seems that by the time the RefactoringTool finishes running some of the
        // compiler/ast information gets lost, so we do it here while we can still do lookups
        clang::SourceManager const* sm = &ci_->getSourceManager();
        clang::LangOptions   lopt = ci_->getLangOpts();
        for ( std::size_t i = 0; i < cond_ranges_.size(); ++i) {
            std::cout << "The range ";
            print_source_range_info(std::cout, sm, cond_ranges_[i]);
            if (cond_ranges_[i].getBegin() == cond_ranges_[i].getEnd()) {
                std::cout << " is empty\n";
                continue;
            }
            if (decls_[i].empty() && stmts_[i].empty()) {
                std::cout << " contains nothing we are interested in\n";
            }
            if (!decls_[i].empty()) {
                std::cout << " contains " << decls_[i].size() << " type declarations:\n";
                for( clang::Decl const * decl : decls_[i] ) {
                    print_source_range(std::cout, sm, lopt, decl->getSourceRange());
                    std::cout << ";\n";
                }
            }
            if (!stmts_[i].empty()) {
                std::cout << " contains " << stmts_[i].size() << " statements:\n";
                for( clang::Stmt const * stmt : stmts_[i] ) {
                    print_source_range(std::cout, sm, lopt, stmt->getSourceRange());
                    std::cout << ";\n";
                }
            }
        }
    }

private:
    std::string mname_;
    std::vector<clang::SourceRange>& cond_ranges_;
    clang::CompilerInstance* ci_;
    RangeNodes<clang::Decl> const & decls_;
    RangeNodes<clang::Stmt> const & stmts_;
            
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
            finder_.addMatcher(
                decl(
                    isExpansionInMainFile(),   // not in an included header
                    declInRange(range),        // within target range
                    anyOf(typedefDecl(), usingDecl()),  // a type declaration
                    decl().bind("target")),
                &decl_handlers_.back());

            // statement matcher
            stmt_nodes_.emplace_back();
            stmt_handlers_.emplace_back(stmt_nodes_.back());
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

int main(int argc, char const **argv) {
    using namespace clang;
    using namespace clang::tooling;
    using namespace clang::ast_matchers;

    if (argc != 3) {
        std::cerr << "usage: " << argv[0] << " MACRO filename\n";
        return 1;
    }
            
    std::string mname(argv[1]);

    /*
     * Prepare to evaluate macro defined condition
     */

    // when tool run completes we will have the following data:
    std::vector<clang::SourceRange> cond_ranges_defined;   // source range for each ifdef
    RangeNodes<clang::Decl> decls_defined;                 // typedefs in each range
    RangeNodes<clang::Stmt> stmts_defined;                 // statements in each range

    // create a fake command line of type Clang tools accept
    std::vector<char const*> args;
    args.push_back(argv[0]);
    args.push_back(argv[2]);
    args.push_back("--");
    std::string define_macro("-D"); define_macro += mname;
    args.push_back(define_macro.c_str());
    int args_c = args.size();
    CommonOptionsParser opt_defined(args_c, args.data(), ToolingSampleCategory);

    // create callbacks for storing the conditional ranges as the preprocessor finds them
    PPCallbacksInstaller<true>      ppci_defined(mname, cond_ranges_defined,
                                                 decls_defined, stmts_defined);

    // use test hook to set up range matchers after preprocessing but before AST visitation
    MatchFinder           finder_defined;
    MatcherInstaller      set_up_source_ranges(finder_defined, cond_ranges_defined,
                                               decls_defined, stmts_defined);
    finder_defined.registerTestCallbackAfterParsing(&set_up_source_ranges);

    // run the tool for the defined case
    RefactoringTool     tool_defined(opt_defined.getCompilations(), opt_defined.getSourcePathList());
    std::cout << "Conditional source ranges for when FOO is defined:\n";
    if (int result = tool_defined.run(newFrontendActionFactory(&finder_defined, &ppci_defined).get())) {
        return result;
    }

    // output results
    return 0;
}
