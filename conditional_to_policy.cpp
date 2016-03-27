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

void print_decorated_source_range(std::ostream& os, clang::SourceManager const* sm,
                                  clang::LangOptions lopt, clang::SourceRange range) {
    auto beg = range.getBegin();
    auto end = range.getEnd();
    os << "From line " << sm->getExpansionLineNumber(beg);
    os << " column " << sm->getExpansionColumnNumber(beg);
    os << " to line " << sm->getExpansionLineNumber(end);
    os << " column " << sm->getExpansionColumnNumber(end) << ":\n";
    os << "===========\n";
    print_source_range(os, sm, lopt, range);
    os << "\n===========\n";
}

struct MyCallbacks : clang::PPCallbacks
{
    MyCallbacks(clang::LangOptions lopt,
                clang::SourceManager & sm,
                std::string mname,
                bool sense,
                std::vector<clang::SourceRange>& cond_ranges)
        : lopt_(lopt), sm_(sm), mname_(mname), sense_(sense), cond_ranges_(cond_ranges) {}

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
            if (start_it->second == sense_) {
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
            if ((start_it->second == sense_) && !else_loc_) {
                cond_ranges_.emplace_back(ifloc, endifloc);
            // - an if of the inverted sense with an else (range is else through here)
            } else if ((start_it->second != sense_) && else_loc_) {
                cond_ranges_.emplace_back(*else_loc_, endifloc);
            // - an if of inverted sense without an else - empty range
            } else if (start_it->second != sense_) {
                cond_ranges_.emplace_back(endifloc, endifloc);
            }
            // - an if of desired sense with else (we found the range when we found the else)
        }
    }        

private:
    clang::LangOptions    lopt_;
    clang::SourceManager& sm_;
    std::string           mname_;
    bool                  sense_;     // true if we want to capture text when mname is defined
    std::map<clang::SourceLocation, bool> cond_starts_;
    std::experimental::optional<clang::SourceLocation> else_loc_;    // most recent "else", if any
    std::vector<clang::SourceRange>& cond_ranges_;

};

struct PPCallbacksInstaller : clang::tooling::SourceFileCallbacks
{
    PPCallbacksInstaller(std::string mname, bool sense, std::vector<clang::SourceRange>& cond_ranges)
        : mname_(mname), sense_(sense), cond_ranges_(cond_ranges), ci_(nullptr) {}

    ~PPCallbacksInstaller() {}

    bool handleBeginSource(clang::CompilerInstance & ci, StringRef fn) override {
        ci_ = &ci;
        // at this point the preprocessor has been initialized, so we cannot add definitions
        // we can, however, set up callbacks
        ci.getPreprocessor().addPPCallbacks(llvm::make_unique<MyCallbacks>(ci.getLangOpts(), ci.getSourceManager(), mname_, sense_, cond_ranges_));
        return true;
    }

private:
    std::string mname_;
    bool        sense_;
    std::vector<clang::SourceRange>& cond_ranges_;
    clang::CompilerInstance* ci_;
            
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

// action for when we find a statement
struct StmtHandler : clang::ast_matchers::MatchFinder::MatchCallback {

    virtual void run(clang::ast_matchers::MatchFinder::MatchResult const& result) {
        std::cout << "found a statement only present when the macro is defined:\n";
        clang::Stmt const * stmt = result.Nodes.getNodeAs<clang::Stmt>("stmt");
        auto const & sm = result.Context->getSourceManager();
        auto lopt = result.Context->getLangOpts();
        print_source_range(std::cout, &sm, lopt, stmt->getSourceRange());
        std::cout << ";\n";
    }
};
            
// action for when we find a declaration
struct DeclHandler : clang::ast_matchers::MatchFinder::MatchCallback {

    virtual void run(clang::ast_matchers::MatchFinder::MatchResult const& result) {
        std::cout << "found a typedef only present when the macro is defined:\n";
        clang::Decl const * decl = result.Nodes.getNodeAs<clang::Decl>("decl");
        auto const & sm = result.Context->getSourceManager();
        auto lopt = result.Context->getLangOpts();
        print_source_range(std::cout, &sm, lopt, decl->getSourceRange());
        std::cout << ";\n";
    }
};
            
// Test hook to install matchers
// We don't know which source ranges we want to find until preprocessing completes,
// which means we have to set up matchers after parsing begins but before AST traversal
// it's a little weird to use this test hook but it's exactly what we need
struct MatcherInstaller : clang::ast_matchers::MatchFinder::ParsingDoneTestCallback {

    MatcherInstaller(clang::ast_matchers::MatchFinder& finder,
                     std::vector<clang::SourceRange> const& ranges)
        : finder_(finder), ranges_(ranges) {}

    virtual void run() override {
        // install matchers for the given ranges into the finder
        using namespace clang::ast_matchers;
        using namespace custom_matchers;
        for( auto const& range : ranges_ ) {
            // statement matcher
            finder_.addMatcher(
                stmt(                          // statement requirements:
                    isExpansionInMainFile(),   // not in an included header
                    statementInRange(range),   // within target range
                    hasParent(
                        compoundStmt()),       // part of compound statement
                    unless(declStmt(           // not a type declaration
                               hasSingleDecl(
                                   anyOf(typedefDecl(), usingDecl())))),
                    stmt().bind("stmt")),       // remember it
                &stmt_handler_);
            // typedef matcher
            finder_.addMatcher(
                decl(
                    isExpansionInMainFile(),
                    declInRange(range),
                    anyOf(typedefDecl(), usingDecl()),
                    decl().bind("decl")),
                &decl_handler_);
        }
    }

private:
    clang::ast_matchers::MatchFinder&      finder_;
    std::vector<clang::SourceRange> const& ranges_;
    StmtHandler                            stmt_handler_;
    DeclHandler                            decl_handler_;
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

    // create a fake command line of type Clang tools accept
    std::vector<char const*> args;
    args.push_back(argv[0]);
    args.push_back(argv[2]);
    args.push_back("--");
    std::string define_macro("-D"); define_macro += mname;
    args.push_back(define_macro.c_str());
    int args_c = args.size();
    CommonOptionsParser opt_defined(args_c, args.data(), ToolingSampleCategory);

    RefactoringTool     tool_defined(opt_defined.getCompilations(), opt_defined.getSourcePathList());

    // prepare to store source ranges for defined case
    std::vector<clang::SourceRange> cond_defined_ranges;
    PPCallbacksInstaller            ppci_defined(mname, true, cond_defined_ranges);

    // use test hook to set up range matchers after preprocessing but before AST visitation
    MatchFinder           finder_defined;
    MatcherInstaller      set_up_source_ranges(finder_defined, cond_defined_ranges);
    finder_defined.registerTestCallbackAfterParsing(&set_up_source_ranges);

    // run the tool for the defined case
    if (int result = tool_defined.run(newFrontendActionFactory(&finder_defined, &ppci_defined).get())) {
        return result;
    }

    return 0;
}
