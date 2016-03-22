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
    MyCallbacks(clang::Preprocessor & pp) : pp_(pp) {}

    void Ifdef(clang::SourceLocation loc,
               clang::Token const& tok,
               clang::MacroDefinition const& md) override {
        std::cerr << "I saw an ifdef: " << tok.getIdentifierInfo()->getName().str() << "\n";
    }
private:
    clang::Preprocessor & pp_;

};

struct PPCallbacksInstaller : clang::tooling::SourceFileCallbacks
{
    ~PPCallbacksInstaller() {}
    bool handleBeginSource(clang::CompilerInstance & ci, StringRef fn) override {
        std::cerr << "begin processing " << fn.str() << "\n";
        auto & pp = ci.getPreprocessor();
        pp.addPPCallbacks(llvm::make_unique<MyCallbacks>(pp));
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
