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
  class VirtualBugVisitor : public BugReporterVisitorImpl<VirtualBugVisitor> {
  private:
    const MemRegion *ObjectRegion;
    bool Found;

  public:
    VirtualBugVisitor(const MemRegion *R) : ObjectRegion(R), Found(false) {}

    void Profile(llvm::FoldingSetNodeID &ID) const override {
      static int X = 0;
      ID.AddPointer(&X);
      ID.AddPointer(ObjectRegion);
    }

    std::shared_ptr<PathDiagnosticPiece> VisitNode(const ExplodedNode *N,
                                                   const ExplodedNode *PrevN,
                                                   BugReporterContext &BRC,
                                                   BugReport &BR) override;
  };
};
}

// GDM (generic data map) to the memregion of this for the ctor and dtor.
REGISTER_MAP_WITH_PROGRAMSTATE(CtorMap, const MemRegion *, bool)
REGISTER_MAP_WITH_PROGRAMSTATE(DtorMap, const MemRegion *, bool)

std::shared_ptr<PathDiagnosticPiece>
VirtualCallChecker::VirtualBugVisitor::VisitNode(const ExplodedNode *N,
                                                 const ExplodedNode *PrevN,
                                                 BugReporterContext &BRC,
                                                 BugReport &BR) {
  // We need the last ctor/dtor which call the virtual function.
  // The visitor walks the ExplodedGraph backwards.
  if (Found)
    return nullptr;

  ProgramStateRef State = N->getState();
  const LocationContext *LCtx = N->getLocationContext();
  ProgramStateManager &PSM = State->getStateManager();
  auto &SVB = PSM.getSValBuilder();
  const CXXConstructorDecl *CD =
      dyn_cast_or_null<CXXConstructorDecl>(LCtx->getDecl());
  const CXXDestructorDecl *DD =
      dyn_cast_or_null<CXXDestructorDecl>(LCtx->getDecl());

  if (!CD && !DD)
    return nullptr;
  const auto *MD = dyn_cast<CXXMethodDecl>(LCtx->getDecl());
  auto ThiSVal =
      State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
  const MemRegion *Reg = ThiSVal.getAsRegion();
  if (Reg != ObjectRegion)
    return nullptr;

  const Stmt *S = PathDiagnosticLocation::getStmt(N);
  if (!S)
    return nullptr;
  Found = true;

  std::string DeclName;
  std::string InfoText;
  if (CD) {
    DeclName = CD->getNameAsString();
    InfoText = "Called from this constrctor '" + DeclName + "'";
  } else {
    DeclName = DD->getNameAsString();
    InfoText = "Called from this destrctor '" + DeclName + "'";
  }

  // Generate the extra diagnostic.
  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return std::make_shared<PathDiagnosticEventPiece>(Pos, InfoText, true);
}

// The function to check if a callexpr is a virtual function.
static bool IsVirtualCall(const CallExpr *CE) {
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

// The BeginFunction callback when enter a constructor or a destructor.
void VirtualCallChecker::checkBeginFunction(CheckerContext &C) const {
  const auto *LCtx = C.getLocationContext();
  const auto *MD = dyn_cast<CXXMethodDecl>(LCtx->getDecl());
  if (!MD)
    return;

  ProgramStateRef State = C.getState();
  auto &SVB = C.getSValBuilder();

  // Enter a constructor, set the corresponding memregion be true.
  if (isa<CXXConstructorDecl>(MD)) {
    auto ThiSVal =
        State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
    const MemRegion *Reg = ThiSVal.getAsRegion();
    State = State->set<CtorMap>(Reg, true);
    C.addTransition(State);
    return;
  }

  // Enter a Destructor, set the corresponding memregion be true.
  if (isa<CXXDestructorDecl>(MD)) {
    auto ThiSVal =
        State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
    const MemRegion *Reg = ThiSVal.getAsRegion();
    State = State->set<DtorMap>(Reg, true);
    C.addTransition(State);
    return;
  }
}

// The EndFunction callback when leave a constructor or a destructor.
void VirtualCallChecker::checkEndFunction(CheckerContext &C) const {
  const auto *LCtx = C.getLocationContext();
  const auto *MD = dyn_cast<CXXMethodDecl>(LCtx->getDecl());
  if (!MD)
    return;

  ProgramStateRef State = C.getState();
  auto &SVB = C.getSValBuilder();

  // Leave a constructor, remove the corresponding memregion.
  if (isa<CXXConstructorDecl>(MD)) {
    auto ThiSVal =
        State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
    const MemRegion *Reg = ThiSVal.getAsRegion();
    State = State->remove<CtorMap>(Reg);
    C.addTransition(State);
    return;
  }

  // Leave a destructor, remove the corresponding memregion.
  if (isa<CXXDestructorDecl>(MD)) {
    auto ThiSVal =
        State->getSVal(SVB.getCXXThis(MD, LCtx->getCurrentStackFrame()));
    const MemRegion *Reg = ThiSVal.getAsRegion();
    State = State->remove<DtorMap>(Reg);
    C.addTransition(State);
    return;
  }
}

void VirtualCallChecker::checkPreCall(const CallEvent &Call,
                                      CheckerContext &C) const {
  const auto MC = dyn_cast<CXXMemberCall>(&Call);
  if (!MC)
    return;

  const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(Call.getDecl());
  ProgramStateRef State = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const MemRegion *Reg = MC->getCXXThisVal().getAsRegion();

  if (IsPureOnly && !MD->isPure())
    return;
  if (!IsVirtualCall(CE))
    return; 

  // Check if a virtual method is called.
  // The GDM of constructor and destructor should be true.
  if (State->get<CtorMap>(Reg)) {
    if (IsPureOnly && MD->isPure()) {
      ExplodedNode *N = C.generateErrorNode();
      if (!N)
        return;
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to pure function during construction", N);
      Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Reg));
      C.emitReport(std::move(Reporter));
      return;
    } else {
      ExplodedNode *N = C.generateNonFatalErrorNode();
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to virtual function during construction", N);
      Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Reg));
      C.emitReport(std::move(Reporter));
      return;
    }
  }

  if (State->get<DtorMap>(Reg)) {
    if (IsPureOnly && MD->isPure()) {
      ExplodedNode *N = C.generateErrorNode();
      if (!N)
        return;
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to pure function during destruction", N);
      Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Reg));
      C.emitReport(std::move(Reporter));
      return;
    } else {
      ExplodedNode *N = C.generateNonFatalErrorNode();
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to virtual function during destruction", N);
      Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Reg));
      C.emitReport(std::move(Reporter));
      return;
    }
  }
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
  VirtualCallChecker *checker = mgr.registerChecker<VirtualCallChecker>();

  checker->IsPureOnly =
      mgr.getAnalyzerOptions().getBooleanOption("PureOnly", false, checker);
}
