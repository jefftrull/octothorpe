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

struct MyCallbacks : clang::PPCallbacks
{
    MyCallbacks(clang::LangOptions lopt, clang::SourceManager & sm) : lopt_(lopt), sm_(sm) {}

    void Ifdef(clang::SourceLocation loc,
               clang::Token const& tok,
               clang::MacroDefinition const& md) override {
        std::cerr << "I saw an ifdef: " << tok.getIdentifierInfo()->getName().str() << "\n";
        std::cerr << "at line " << sm_.getExpansionLineNumber(loc) << " column " << sm_.getExpansionColumnNumber(loc) << "\n";
        // check for our target macro and sense
        // if ((tok.getIdentifierInfo()->getName().str() == tgt_macro_) && sense_) {
    }

    void Ifndef(clang::SourceLocation loc,
                clang::Token const& tok,
                clang::MacroDefinition const& md) override {
        std::cerr << "I saw an ifndef: " << tok.getIdentifierInfo()->getName().str() << "\n";
        std::cerr << "at line " << sm_.getExpansionLineNumber(loc) << " column " << sm_.getExpansionColumnNumber(loc) << "\n";
    }

    // else and endif are reported as long as their corresponding if is not *within* a skipped region

    void Else(clang::SourceLocation elseloc,
              clang::SourceLocation ifloc) override {
        std::cerr << "I found an else at line ";
        std::cerr << sm_.getExpansionLineNumber(elseloc) << " column " << sm_.getExpansionColumnNumber(elseloc);
        std::cerr << " related to an if at line ";
        std::cerr << sm_.getExpansionLineNumber(ifloc) << " column " << sm_.getExpansionColumnNumber(ifloc) << "\n";
    }        

    void Endif(clang::SourceLocation endifloc,
               clang::SourceLocation ifloc) override {
        std::cerr << "I found an endif at line ";
        std::cerr << sm_.getExpansionLineNumber(endifloc) << " column " << sm_.getExpansionColumnNumber(endifloc);
        std::cerr << " that terminates an if at line ";
        std::cerr << sm_.getExpansionLineNumber(ifloc) << " column " << sm_.getExpansionColumnNumber(ifloc) << "\n";
    }        

    // we won't see the tokens inside here except for the final else/endif
    void SourceRangeSkipped(clang::SourceRange rng) override {
        std::cerr << "I skipped a source range, from line ";
        std::cerr << sm_.getExpansionLineNumber(rng.getBegin()) << " column " << sm_.getExpansionColumnNumber(rng.getBegin());
        std::cerr << " to line ";
        std::cerr << sm_.getExpansionLineNumber(rng.getEnd()) << " column " << sm_.getExpansionColumnNumber(rng.getEnd()) << "\n";
    }

private:
    clang::LangOptions lopt_;
    clang::SourceManager& sm_;

};

struct PPCallbacksInstaller : clang::tooling::SourceFileCallbacks
{
    ~PPCallbacksInstaller() {}
    bool handleBeginSource(clang::CompilerInstance & ci, StringRef fn) override {
        std::cerr << "begin processing " << fn.str() << "\n";
        ci.getPreprocessor().addPPCallbacks(llvm::make_unique<MyCallbacks>(ci.getLangOpts(), ci.getSourceManager()));

        return true;
    }
};

int main(int argc, char const **argv) {
    using namespace clang;
    using namespace clang::tooling;
    using namespace clang::ast_matchers;

    CommonOptionsParser opt(argc, argv, ToolingSampleCategory);
    RefactoringTool     tool(opt.getCompilations(), opt.getSourcePathList());

    MatchFinder         finder;
    PPCallbacksInstaller ppci;
    if (int result = tool.run(newFrontendActionFactory(&finder, &ppci).get())) {
        return result;
    }

    std::cout << "Collected replacements:\n";
    for (auto const & r : tool.getReplacements()) {
        std::cout << r.toString() << "\n";
    }

    return 0;
}
