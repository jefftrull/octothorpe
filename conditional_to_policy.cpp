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

struct MyCallbacks : clang::PPCallbacks
{
    MyCallbacks(clang::LangOptions lopt,
                clang::SourceManager & sm,
                std::string mname,
                bool sense)
        : lopt_(lopt), sm_(sm), mname_(mname), sense_(sense) {}

    void Ifdef(clang::SourceLocation loc,
               clang::Token const& tok,
               clang::MacroDefinition const& md) override {
        // check for our target macro and sense
        if (tok.getIdentifierInfo()->getName().str() == mname_) {
            cond_starts_.emplace(loc, true);
            else_loc_ = std::experimental::nullopt;
            if (sense_) {
                std::cerr << "I saw an ifdef: " << tok.getIdentifierInfo()->getName().str() << "\n";
                std::cerr << "at line " << sm_.getExpansionLineNumber(loc) << " column " << sm_.getExpansionColumnNumber(loc) << "\n";
            }
        }
    }

    void Ifndef(clang::SourceLocation loc,
                clang::Token const& tok,
                clang::MacroDefinition const& md) override {
        if (tok.getIdentifierInfo()->getName().str() == mname_) {
            cond_starts_.emplace(loc, false);
            else_loc_ = std::experimental::nullopt;
            if (!sense_) {
                std::cerr << "I saw an ifndef: " << tok.getIdentifierInfo()->getName().str() << "\n";
                std::cerr << "at line " << sm_.getExpansionLineNumber(loc) << " column " << sm_.getExpansionColumnNumber(loc) << "\n";
            }
        }
    }

    // else and endif are reported as long as their corresponding if is not *within* a skipped region

    void Else(clang::SourceLocation elseloc,
              clang::SourceLocation ifloc) override {
        // see if this else is related to an ifdef/ifndef for our target macro
        auto start_it = cond_starts_.find(ifloc);
        if (start_it != cond_starts_.end()) {
            std::cerr << "I found an else at line ";
            std::cerr << sm_.getExpansionLineNumber(elseloc) << " column " << sm_.getExpansionColumnNumber(elseloc);
            if (start_it->second == sense_) {
                // this is the *end* of our range of interest
                std::cerr << " which ends the range of interest that began at line ";
                std::cerr << sm_.getExpansionLineNumber(ifloc) << " column " << sm_.getExpansionColumnNumber(ifloc) << "\n";
            } else {
                // this is the *start* of our range, because the sense of the original was inverted
                std::cerr << " which begins a range of interest\n";
            }
            else_loc_ = elseloc;
        }
    }        

    void Endif(clang::SourceLocation endifloc,
               clang::SourceLocation ifloc) override {
        auto start_it = cond_starts_.find(ifloc);
        if (start_it != cond_starts_.end()) {
            std::cerr << "I found an endif at line ";
            std::cerr << sm_.getExpansionLineNumber(endifloc) << " column " << sm_.getExpansionColumnNumber(endifloc);
            // this endif may terminate:
            // - an if of the desired sense without an else (range is ifloc through here)
            // - an if of the inverted sense with an else (range is else through here)
            // - an if of desired sense with else (we found the range when we found the else)
            // - an if inverted sense without an else - output empty range
            if (((start_it->second != sense_) && else_loc_) ||
                ((start_it->second == sense_) && !else_loc_)) {
                std::cerr << " that ends the range of interest that began at line ";
                if (else_loc_) {
                    std::cerr << sm_.getExpansionLineNumber(*else_loc_) << " column " << sm_.getExpansionColumnNumber(*else_loc_) << "\n";
                } else {
                    std::cerr << sm_.getExpansionLineNumber(ifloc) << " column " << sm_.getExpansionColumnNumber(ifloc) << "\n";
                }                    
            } else if (start_it->second != sense_) {
                std::cerr << " which marks an empty range (inverted sense, no else)\n";
            }
        }
    }        

    // we won't see the tokens inside here except for the final else/endif
    void SourceRangeSkipped(clang::SourceRange rng) override {
        std::cerr << "I skipped a source range, from line ";
        std::cerr << sm_.getExpansionLineNumber(rng.getBegin()) << " column " << sm_.getExpansionColumnNumber(rng.getBegin());
        std::cerr << " to line ";
        std::cerr << sm_.getExpansionLineNumber(rng.getEnd()) << " column " << sm_.getExpansionColumnNumber(rng.getEnd()) << "\n";
    }

private:
    clang::LangOptions    lopt_;
    clang::SourceManager& sm_;
    std::string           mname_;
    bool                  sense_;     // true if we want to capture text when mname is defined
    std::map<clang::SourceLocation, bool> cond_starts_;
    std::experimental::optional<clang::SourceLocation> else_loc_;    // most recent "else", if any

};

struct PPCallbacksInstaller : clang::tooling::SourceFileCallbacks
{
    ~PPCallbacksInstaller() {}
    bool handleBeginSource(clang::CompilerInstance & ci, StringRef fn) override {
        std::cerr << "begin processing " << fn.str() << "\n";
        ci.getPreprocessor().addPPCallbacks(llvm::make_unique<MyCallbacks>(ci.getLangOpts(), ci.getSourceManager(), "FOO", true));
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
