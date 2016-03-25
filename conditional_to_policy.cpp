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

void print_source_range(std::ostream& os, clang::SourceManager* sm,
                        clang::LangOptions lopt, clang::SourceRange range) {
    auto beg = range.getBegin();
    auto end = range.getEnd();
    os << "From line " << sm->getExpansionLineNumber(beg);
    os << " column " << sm->getExpansionColumnNumber(beg);
    os << " to line " << sm->getExpansionLineNumber(end);
    os << " column " << sm->getExpansionColumnNumber(end) << ":\n";
    os << "===========\n#";
    clang::SourceLocation true_end =
        clang::Lexer::getLocForEndOfToken(end, 0, *sm, lopt);
    os << std::string(sm->getCharacterData(beg),
                             sm->getCharacterData(true_end) - sm->getCharacterData(beg));
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
        std::cerr << "begin processing " << fn.str() << "\n";
        ci.getPreprocessor().addPPCallbacks(llvm::make_unique<MyCallbacks>(ci.getLangOpts(), ci.getSourceManager(), mname_, sense_, cond_ranges_));
        return true;
    }

    void handleEndSource() override {
        std::cout << "Source ranges present only when " << mname_ << " is ";
        std::cout << (sense_ ? "defined" : "not defined") << ":\n";
                      
        for (auto const & range : cond_ranges_) {
            print_source_range(std::cout, &ci_->getSourceManager(), ci_->getLangOpts(), range);
        }
    }            

private:
    std::string mname_;
    bool        sense_;
    std::vector<clang::SourceRange>& cond_ranges_;
    clang::CompilerInstance* ci_;
            
};

int main(int argc, char const **argv) {
    using namespace clang;
    using namespace clang::tooling;
    using namespace clang::ast_matchers;

    CommonOptionsParser opt(argc, argv, ToolingSampleCategory);
    RefactoringTool     tool(opt.getCompilations(), opt.getSourcePathList());

    MatchFinder         finder;
    std::vector<clang::SourceRange> cond_true_ranges;
    PPCallbacksInstaller ppci("FOO", true, cond_true_ranges);
    if (int result = tool.run(newFrontendActionFactory(&finder, &ppci).get())) {
        return result;
    }

    std::cout << "Collected replacements:\n";
    for (auto const & r : tool.getReplacements()) {
        std::cout << r.toString() << "\n";
    }

    return 0;
}
