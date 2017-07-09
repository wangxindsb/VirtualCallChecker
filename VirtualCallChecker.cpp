//=======- VirtualCallChecker.cpp --------------------------------*- C++ -*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines a checker that checks virtual function calls during
//  construction or destruction of C++ objects.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/AST/DeclCXX.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SValBuilder.h"

using namespace clang;
using namespace ento;

namespace {

class VirtualCallChecker
    : public Checker<check::BeginFunction, check::EndFunction, check::PreCall> {
  mutable std::unique_ptr<BugType> BT;

public:
  // The flag to determine if pure virtual functions should be issued only.
  DefaultBool IsPureOnly;

  void checkBeginFunction(CheckerContext &C) const;
  void checkEndFunction(CheckerContext &C) const;
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;

private:
  bool IsVirtualCall(const CallExpr *CE) const;
};
}

// GDM (generic data map) to the memregion of this for the ctor and dtor.
REGISTER_MAP_WITH_PROGRAMSTATE(CtorMap, const MemRegion *, bool)
REGISTER_MAP_WITH_PROGRAMSTATE(DtorMap, const MemRegion *, bool)

void VirtualCallChecker::checkBeginFunction(CheckerContext &C) const {
  const auto *LCtx = C.getLocationContext();
  const auto *MD = dyn_cast<CXXMethodDecl>(LCtx->getDecl());
  if (!MD)
    return;

  ProgramStateRef State = C.getState();

  // Enter a constructor, increase the corresponding integer
  if (isa<CXXConstructorDecl>(MD)) {
    auto &SVB = C.getSValBuilder();
    auto ThiSVal = State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
    const MemRegion *Reg = ThiSVal.getAsRegion();
    State = State->set<CtorMap>(Reg, true);
    C.addTransition(State); 
    return;
  }

  // Enter a Destructor, increase the corresponding integer
  if (isa<CXXDestructorDecl>(MD)) {
    auto &SVB = C.getSValBuilder();
    auto ThiSVal = State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
    const MemRegion *Reg = ThiSVal.getAsRegion();
    State = State->set<DtorMap>(Reg, true);
    C.addTransition(State);
    return;
  }
}

// The PostCall callback, when leave a constructor or a destructor,
// decrease the corresponding integer
void VirtualCallChecker::checkEndFunction(CheckerContext &C) const {
  const auto *LCtx = C.getLocationContext();
  const auto *MD = dyn_cast<CXXMethodDecl>(LCtx->getDecl());
  if (!MD)
    return;

  ProgramStateRef State = C.getState();

  if (isa<CXXConstructorDecl>(MD)) {
    auto &SVB = C.getSValBuilder();
    auto ThiSVal = State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
    const MemRegion *Reg = ThiSVal.getAsRegion();
    State = State->remove<CtorMap>(Reg);
    C.addTransition(State);
    return;
  }

  if (isa<CXXDestructorDecl>(MD)) {
    auto &SVB = C.getSValBuilder();
    auto ThiSVal = State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
    const MemRegion *Reg = ThiSVal.getAsRegion();
    State = State->remove<DtorMap>(Reg);
    C.addTransition(State);
    return;
  }
}

void VirtualCallChecker::checkPreCall(const CallEvent &Call,
                                      CheckerContext &C) const {
  const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(Call.getDecl());
  if (!MD)
    return;
  
  if (isa<CXXConstructorDecl>(MD) || isa<CXXDestructorDecl>(MD))
    return;

  const auto IC = dyn_cast<CXXInstanceCall>(&Call);
  if (!IC)
    return;

  ProgramStateRef State = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const MemRegion *Reg = IC->getCXXThisVal().getAsRegion();

  // Check if a virtual method is called.
  // The GDM of constructor and destructor should be larger than 0.
  if (IsPureOnly && !MD->isPure())
    return;

  if (IsVirtualCall(CE) && State->get<CtorMap>(Reg)) {
    if (IsPureOnly && MD->isPure()) {
      ExplodedNode *N = C.generateErrorNode();
      if (!N)
        return;
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to pure function during construction", N);
      C.emitReport(std::move(Reporter));
      return;
    } else {
      ExplodedNode *N = C.generateNonFatalErrorNode();
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));
      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to virtual function during construction", N);
      C.emitReport(std::move(Reporter));
      return;
    }
  }

  if (IsVirtualCall(CE) && State->get<DtorMap>(Reg)) {
    if (IsPureOnly && MD->isPure()) {
      ExplodedNode *N = C.generateErrorNode();
      if (!N)
        return;
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to pure function during destruction", N);
      C.emitReport(std::move(Reporter));
      return;
    } else {
      ExplodedNode *N = C.generateNonFatalErrorNode();
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to virtual function during destruction", N);
      C.emitReport(std::move(Reporter));
      return;
    }
  }
}

// The function to check if a callexpr is a virtual function.
bool VirtualCallChecker::IsVirtualCall(const CallExpr *CE) const {
  bool CallIsNonVirtual = false;

  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    // The member access is fully qualified (i.e., X::F).
    // Treat this as a non-virtual call and do not warn.
    if (CME->getQualifier())
      CallIsNonVirtual = true;

    if (const Expr *Base = CME->getBase()->IgnoreImpCasts()) {
      // The most derived class is marked final.
      if (Base->getBestDynamicClassType()->hasAttr<FinalAttr>())
        CallIsNonVirtual = true;
    }
  }

  const CXXMethodDecl *MD =
      dyn_cast_or_null<CXXMethodDecl>(CE->getDirectCallee());
  if (MD && MD->isVirtual() && !CallIsNonVirtual && !MD->hasAttr<FinalAttr>() &&
      !MD->getParent()->hasAttr<FinalAttr>())
    return true;
  return false;
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
  VirtualCallChecker *checker = mgr.registerChecker<VirtualCallChecker>();

  checker->IsPureOnly =
      mgr.getAnalyzerOptions().getBooleanOption("PureOnly", false, checker);
}
