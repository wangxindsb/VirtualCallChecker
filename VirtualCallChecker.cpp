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
    : public Checker<check::BeginFunction, check::EndFunction, check::PreCall,
                     check::PostCall> {
  mutable std::unique_ptr<BugType> BT;

public:
  // The flag to determine if pure virtual functions should be issued only.
  DefaultBool IsPureOnly;

  void checkBeginFunction(CheckerContext &C) const;
  void checkEndFunction(CheckerContext &C) const;
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  bool IsCalledbyCtor(const CallExpr *CE, ProgramStateRef State,
                      const LocationContext *LCtx) const;
  bool IsCalledbyDtor(const CallExpr *CE, ProgramStateRef State,
                      const LocationContext *LCtx) const;

private:
  bool IsVirtualCall(const CallExpr *CE) const;
  Optional<SVal> getThisSVal(const StackFrameContext *SFC,
                             const ProgramStateRef State) const;

  class VirtualBugVisitor : public BugReporterVisitorImpl<VirtualBugVisitor> {
  private:
    const unsigned TrackedCtorDtorFlag;
    bool Found;

  public:
    VirtualBugVisitor(const unsigned TrackedCtorDtorFlag)
        : TrackedCtorDtorFlag(TrackedCtorDtorFlag), Found(false) {}
    void Profile(llvm::FoldingSetNodeID &ID) const override {
      static int x = 0;
      ID.AddPointer(&x);
      ID.AddPointer(&TrackedCtorDtorFlag);
    }
    std::shared_ptr<PathDiagnosticPiece> VisitNode(const ExplodedNode *N,
                                                   const ExplodedNode *PrevN,
                                                   BugReporterContext &BRC,
                                                   BugReport &BR) override;
  };
};
}

// GDM (generic data map) to store two integers in the program State.
// One integer for constructors, one integer for destructors.
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstructorFlag, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(DestructorFlag, unsigned)
// GDM (generic data map) to determine if a function is called by an object.
REGISTER_TRAIT_WITH_PROGRAMSTATE(ObjectFlag, unsigned)
// GDM (generic data map) to the memregion of this for the ctor and dtor.
REGISTER_MAP_WITH_PROGRAMSTATE(CtorMap, const MemRegion *, unsigned)
REGISTER_MAP_WITH_PROGRAMSTATE(DtorMap, const MemRegion *, unsigned)

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
  const unsigned Ctorflag = State->get<ConstructorFlag>();
  const unsigned Dtorflag = State->get<DestructorFlag>();
  const LocationContext *LCtx = N->getLocationContext();
  const CXXConstructorDecl *CD =
      dyn_cast_or_null<CXXConstructorDecl>(LCtx->getDecl());
  const CXXDestructorDecl *DD =
      dyn_cast_or_null<CXXDestructorDecl>(LCtx->getDecl());

  if ((!CD && !DD) ||
      (Ctorflag != TrackedCtorDtorFlag && Dtorflag != TrackedCtorDtorFlag))
    return nullptr;

  const Stmt *S = PathDiagnosticLocation::getStmt(N);
  if (!S)
    return nullptr;
  Found = true;

  std::string DeclName;
  std::string InfoText;
  if (CD) {
    DeclName = CD->getNameAsString();
    InfoText = "Called from this constrctor " + DeclName;
  } else {
    DeclName = DD->getNameAsString();
    InfoText = "called from this destructor " + DeclName;
  }

  // Generate the extra diagnostic.
  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return std::make_shared<PathDiagnosticEventPiece>(Pos, InfoText, true);
}

void VirtualCallChecker::checkBeginFunction(CheckerContext &C) const {
  const auto *LCtx = C.getLocationContext();
  const auto *MD = dyn_cast<CXXMethodDecl>(LCtx->getDecl());
  if (!MD)
    return;

  ProgramStateRef State = C.getState();

  // Enter a constructor, increase the corresponding integer
  if (isa<CXXConstructorDecl>(MD)) {
    unsigned Constructorflag = State->get<ConstructorFlag>();
    State = State->set<ConstructorFlag>(++Constructorflag);
    C.addTransition(State);
    return;
  }

  // Enter a Destructor, increase the corresponding integer
  if (isa<CXXDestructorDecl>(MD)) {
    unsigned Destructorflag = State->get<DestructorFlag>();
    State = State->set<DestructorFlag>(++Destructorflag);
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
    unsigned Constructorflag = State->get<ConstructorFlag>();
    State = State->set<ConstructorFlag>(--Constructorflag);
    C.addTransition(State);
    return;
  }

  if (isa<CXXDestructorDecl>(MD)) {
    unsigned Destructorflag = State->get<DestructorFlag>();
    State = State->set<DestructorFlag>(--Destructorflag);
    C.addTransition(State);
    return;
  }
}

void VirtualCallChecker::checkPreCall(const CallEvent &Call,
                                      CheckerContext &C) const {
  const Decl *D = Call.getDecl();
  if (!D)
    return;

  const auto *CC = dyn_cast<CXXConstructorCall>(&Call);
  const auto *CD = dyn_cast<CXXDestructorCall>(&Call);

  ProgramStateRef State = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LCtx = C.getLocationContext();
  const StackFrameContext *SFC = LCtx->getCurrentStackFrame();

  Optional<SVal> ThisSVal = getThisSVal(SFC, State);
  const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(D);

  // Enter a constructor, increase the corresponding integer.
  if (isa<CXXConstructorDecl>(D)) {
    if (!CC)
      return;
    const MemRegion *Reg = CC->getCXXThisVal().getAsRegion();
    State = State->set<CtorMap>(Reg, 1);
    C.addTransition(State);
    return;
  }

  // Enter a Destructor, increase the corresponding integer.
  if (isa<CXXDestructorDecl>(D)) {
    if (!CD)
      return;
    const MemRegion *Reg = CD->getCXXThisVal().getAsRegion();
    State = State->set<DtorMap>(Reg, 1);
    C.addTransition(State);
    return;
  }

  // Set the Objectflag.
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    // The member access is fully qualified (i.e., X::F).
    // Treat this as a non-virtual call and do not warn.
    if (const Expr *Base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(Base)) {
        SVal CEV = State->getSVal(Base, LCtx);
        if (CEV != ThisSVal) {
          unsigned Objectflag = State->get<ObjectFlag>();
          State = State->set<ObjectFlag>(++Objectflag);
          C.addTransition(State);
        }
      }
    }
  }

  // Check if a virtual method is called.
  // The GDM of constructor and destructor should be larger than 0.
  if (IsPureOnly && !MD->isPure())
    return;

  if (IsVirtualCall(CE) && State->get<ConstructorFlag>() > 0 &&
      (State->get<ObjectFlag>() == 0 ||
       (State->get<ObjectFlag>() > 0 && IsCalledbyCtor(CE, State, LCtx)))) {
    if (IsPureOnly && MD->isPure()) {
      ExplodedNode *N = C.generateErrorNode();
      if (!N)
        return;
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to pure function during construction", N);
      const unsigned Ctorflag = State->get<ConstructorFlag>();
      Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Ctorflag));
      C.emitReport(std::move(Reporter));
      return;
    } else {
      ExplodedNode *N = C.generateNonFatalErrorNode();
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));
      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to virtual function during construction", N);
      const unsigned Ctorflag = State->get<ConstructorFlag>();
      Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Ctorflag));
      C.emitReport(std::move(Reporter));
      return;
    }
  }

  if (IsVirtualCall(CE) && State->get<DestructorFlag>() > 0 &&
      (State->get<ObjectFlag>() == 0 ||
       (State->get<ObjectFlag>() > 0 && IsCalledbyDtor(CE, State, LCtx)))) {
    if (IsPureOnly && MD->isPure()) {
      ExplodedNode *N = C.generateErrorNode();
      if (!N)
        return;
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to pure function during destruction", N);
      const unsigned Dtorflag = State->get<DestructorFlag>();
      Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Dtorflag));
      C.emitReport(std::move(Reporter));
      return;
    } else {
      ExplodedNode *N = C.generateNonFatalErrorNode();
      if (!BT)
        BT.reset(new BugType(this, "Virtual Call", "Path-Sensitive"));

      auto Reporter = llvm::make_unique<BugReport>(
          *BT, "Call to virtual function during destruction", N);
      const unsigned Dtorflag = State->get<DestructorFlag>();
      Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Dtorflag));
      C.emitReport(std::move(Reporter));
      return;
    }
  }
}

// When leave a constructor or a destructor,decrease the corresponding integer.
void VirtualCallChecker::checkPostCall(const CallEvent &Call,
                                       CheckerContext &C) const {
  const Decl *D = Call.getDecl();
  if (!D)
    return;

  const auto *CC = dyn_cast<CXXConstructorCall>(&Call);
  const auto *CD = dyn_cast<CXXDestructorCall>(&Call);

  ProgramStateRef State = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LCtx = C.getLocationContext();
  const StackFrameContext *SFC = LCtx->getCurrentStackFrame();

  Optional<SVal> ThisSVal = getThisSVal(SFC, State);

  if (isa<CXXConstructorDecl>(D)) {
    const MemRegion *Reg = CC->getCXXThisVal().getAsRegion();
    State = State->remove<CtorMap>(Reg);
    C.addTransition(State);
    return;
  }

  if (isa<CXXDestructorDecl>(D)) {
    const MemRegion *Reg = CD->getCXXThisVal().getAsRegion();
    State = State->remove<DtorMap>(Reg);
    C.addTransition(State);
    return;
  }

  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (const Expr *Base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(Base)) {
        SVal CEV = State->getSVal(Base, LCtx);
        if (CEV != ThisSVal) {
          unsigned Objectflag = State->get<ObjectFlag>();
          State = State->set<ObjectFlag>(--Objectflag);
          C.addTransition(State);
        }
      }
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

// Get the SVal of the "this" object for a method call in the given stackframe.
// Returns None if the stack frame does not represent a method call.
Optional<SVal>
VirtualCallChecker::getThisSVal(const StackFrameContext *SFC,
                                const ProgramStateRef State) const {
  if (SFC->inTopFrame()) {
    const FunctionDecl *FD = SFC->getDecl()->getAsFunction();
    if (!FD)
      return None;
    const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(FD->getParent());
    if (!MD)
      return None;
    Loc ThisLoc = State->getStateManager().getSValBuilder().getCXXThis(MD, SFC);
    return State->getSVal(ThisLoc);
  } else {
    const Stmt *S = SFC->getCallSite();
    if (!S)
      return None;
    if (const CXXMemberCallExpr *MCE = dyn_cast_or_null<CXXMemberCallExpr>(S))
      return State->getSVal(MCE->getImplicitObjectArgument(), SFC->getParent());
    else if (const CXXConstructExpr *CCE =
                 dyn_cast_or_null<CXXConstructExpr>(S))
      return State->getSVal(CCE, SFC->getParent());
    return None;
  }
}

// Check the base of the callexpr is equal to the this of the ctor.
bool VirtualCallChecker::IsCalledbyCtor(const CallExpr *CE,
                                        ProgramStateRef State,
                                        const LocationContext *LCtx) const {
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (const Expr *Base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(Base)) {
        SVal CEV = State->getSVal(Base, LCtx);
        CtorMapTy Regmap = State->get<CtorMap>();
        for (CtorMapTy::iterator I = Regmap.begin(), E = Regmap.end(); I != E;
             ++I) {
          const MemRegion *Curreg = I->first;
          SVal CurSV = State->getSVal(Curreg);
          if (CEV == CurSV)
            return true;
        }
      }
    }
  }
  return false;
}

// Check the base of the callexpr is equal to the this of the dtor.
bool VirtualCallChecker::IsCalledbyDtor(const CallExpr *CE,
                                        ProgramStateRef State,
                                        const LocationContext *LCtx) const {
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (const Expr *Base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(Base)) {
        SVal CEV = State->getSVal(Base, LCtx);
        DtorMapTy Regmap = State->get<CtorMap>();
        for (DtorMapTy::iterator I = Regmap.begin(), E = Regmap.end(); I != E;
             ++I) {
          const MemRegion *Curreg = I->first;
          SVal CurSV = State->getSVal(Curreg);
          if (CEV == CurSV)
            return true;
        }
      }
    }
  }
  return false;
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
  VirtualCallChecker *checker = mgr.registerChecker<VirtualCallChecker>();

  checker->IsPureOnly =
      mgr.getAnalyzerOptions().getBooleanOption("PureOnly", false, checker);
}
