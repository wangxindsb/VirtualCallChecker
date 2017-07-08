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

class VirtualCallChecker: public Checker<check::PreCall, check::PostCall> {
  mutable std::unique_ptr<BugType> BT_CT;
  mutable std::unique_ptr<BugType> BT_DT;

public:
  // The flag to determine if pure virtual functions should be issued only
  DefaultBool isPureOnly;

  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  bool isCalledbyCtor(const CallExpr *CE,ProgramStateRef state,const LocationContext *LCtx) const;
  bool isCalledbyDtor(const CallExpr *CE,ProgramStateRef state,const LocationContext *LCtx) const;

private:
  bool isVirtualCall(const CallExpr *CE) const;
  Optional<SVal> getThisSVal(const StackFrameContext *SFC,const ProgramStateRef State) const;

  class VirtualBugVisitor : public BugReporterVisitorImpl<VirtualBugVisitor> {
  private:
    const unsigned TrackedCtorDtorFlag;
    bool Found;
  public:
    VirtualBugVisitor(const unsigned TrackedCtorDtorFlag) : 
      TrackedCtorDtorFlag(TrackedCtorDtorFlag), Found(false) {}
    void Profile(llvm::FoldingSetNodeID &ID) const override{
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

//GDM (generic data map) to store two integers in the program State. 
//One integer for constructors, one integer for destructors.
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstructorFlag, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(DestructorFlag, unsigned)
//GDM (generic data map) to determine if a function is called by an object
REGISTER_TRAIT_WITH_PROGRAMSTATE(ObjectFlag, unsigned)
//GDM (generic data map) to the memregion of this for the ctor and dtor
REGISTER_MAP_WITH_PROGRAMSTATE(CtorMap, const MemRegion*, unsigned)
REGISTER_MAP_WITH_PROGRAMSTATE(DtorMap, const MemRegion*, unsigned)

std::shared_ptr<PathDiagnosticPiece>
VirtualCallChecker::VirtualBugVisitor::VisitNode(const ExplodedNode *N,
                                                 const ExplodedNode *PrevN,
                                                 BugReporterContext &BRC,
                                                 BugReport &BR) {
  // We need the last ctor/dtor which call the virtual function
  // The visitor walks the ExplodedGraph backwards.
  if (Found)
    return nullptr;

  ProgramStateRef State = N->getState();
  const unsigned Ctorflag = State->get<ConstructorFlag>();
  const unsigned Dtorflag = State->get<DestructorFlag>();
  const LocationContext* LCtx = N->getLocationContext();
  const CXXConstructorDecl *CD =
        dyn_cast_or_null<CXXConstructorDecl>(LCtx->getDecl());
  const CXXDestructorDecl *DD =
        dyn_cast_or_null<CXXDestructorDecl>(LCtx->getDecl()); 
 
  if((!CD && !DD) || (Ctorflag!=TrackedCtorDtorFlag && 
      Dtorflag!=TrackedCtorDtorFlag)) 
    return nullptr;
  
  const Stmt *S = PathDiagnosticLocation::getStmt(N); 
  if (!S)
    return nullptr;
  Found = true;

  std::string DeclName;
  std::string InfoText;
  if(CD) {
    DeclName = CD->getNameAsString();
    InfoText = "Called from this constrctor " + DeclName;
  }
  else {
    DeclName = DD->getNameAsString();
    InfoText = "called from this destructor " + DeclName;
  }

  // Generate the extra diagnostic.
  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return std::make_shared<PathDiagnosticEventPiece>(Pos, InfoText, true);
}

void VirtualCallChecker::checkPreCall(const CallEvent &Call, 
                                      CheckerContext &C) const {

  const Decl *D = Call.getDecl();
  if (!D)
    return;

  const auto *CC = dyn_cast_or_null<CXXConstructorCall>(&Call);
  const auto *CD = dyn_cast_or_null<CXXDestructorCall>(&Call);

  ProgramStateRef State = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LCtx = C.getLocationContext();
  const StackFrameContext *SFC = LCtx->getCurrentStackFrame();

  Optional<SVal> ThisSVal = getThisSVal(SFC,State);
  const CXXMethodDecl *MD = dyn_cast_or_null<CXXMethodDecl>(D);

  // Enter a constructor, increase the corresponding integer
  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned Constructorflag = State->get<ConstructorFlag>();
    State = State->set<ConstructorFlag>(++Constructorflag);
    C.addTransition(State);
    if (!CC) return; 
    const MemRegion *reg = CC->getCXXThisVal().getAsRegion();
    State = State->set<CtorMap>(reg,1);
    C.addTransition(State);
    return;
  }

  // Enter a Destructor, increase the corresponding integer
  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned Destructorflag = State->get<DestructorFlag>();
    State = State->set<DestructorFlag>(++Destructorflag);
    C.addTransition(State);
    if (!CD) return; 
    const MemRegion *reg = CD->getCXXThisVal().getAsRegion();
    State = State->set<DtorMap>(reg,1);
    C.addTransition(State);
    return;
  }

  // Set the Objectflag
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    // If the member access is fully qualified (i.e., X::F), then treat
    // this as a non-virtual call and do not warn.
    if (Expr *Base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(Base)) {
        SVal CEV = State->getSVal(Base, LCtx);
        if(CEV != ThisSVal){
          unsigned objectflag = State->get<ObjectFlag>();
          State = State->set<ObjectFlag>(++objectflag);
          C.addTransition(State);
        }
      }
    }
  } 

  // First Check if a virtual method is called, then check the 
  // GDM of constructor and destructor. 
  if (isPureOnly && !MD->isPure()) return;

  if (isVirtualCall(CE) && State->get<ConstructorFlag>() > 0 && 
      (State->get<ObjectFlag>() == 0 || (State->get<ObjectFlag>() > 0 && 
                                         isCalledbyCtor(CE,State,LCtx)))) {
    if (!BT_CT) {
      if (isPureOnly && MD->isPure()) {
      BT_CT.reset(new BugType(this, 
                  "Call to pure function during construction", "pure only"));
      }
      else {
      BT_CT.reset(new BugType(this, 
                  "Call to virtual function during construction", "not pure"));
      }
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
    const unsigned Ctorflag = State->get<ConstructorFlag>(); 
    Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Ctorflag));
    C.emitReport(std::move(Reporter));
    return;
  }

  if (isVirtualCall(CE) && State->get<DestructorFlag>() > 0 && 
      (State->get<ObjectFlag>() == 0 || (State->get<ObjectFlag>() > 0 && 
                                         isCalledbyDtor(CE,State,LCtx)))) {
    if (!BT_DT) {
      if (isPureOnly && MD->isPure()) {
      BT_DT.reset(new BugType(this, 
                  "Call to pure function during destruction", "pure only"));
      }
      else {
      BT_DT.reset(new BugType(this, 
                  "Call to virtual function during destruction", "not pure"));
      }
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_DT, BT_DT->getName(), N);
    const unsigned Dtorflag = State->get<DestructorFlag>(); 
    Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(Dtorflag));
    C.emitReport(std::move(Reporter));
    return;
  }
}

// The PostCall callback, when leave a constructor or a destructor, 
// decrease the corresponding integer
void VirtualCallChecker::checkPostCall(const CallEvent &Call, 
                                       CheckerContext &C) const {

  const Decl *D = Call.getDecl();
  if (!D)
    return;

  const auto *CC = dyn_cast_or_null<CXXConstructorCall>(&Call);
  const auto *CD = dyn_cast_or_null<CXXDestructorCall>(&Call);

  ProgramStateRef State = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LCtx = C.getLocationContext();
  const StackFrameContext *SFC = LCtx->getCurrentStackFrame();

  Optional<SVal> ThisSVal = getThisSVal(SFC,State);

  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned Constructorflag = State->get<ConstructorFlag>();
    State = State->set<ConstructorFlag>(--Constructorflag);
    C.addTransition(State);
    const MemRegion *reg = CC->getCXXThisVal().getAsRegion();
    State = State->remove<CtorMap>(reg);  
    C.addTransition(State);
    return;
  }

  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned Destructorflag = State->get<DestructorFlag>();
    State = State->set<DestructorFlag>(--Destructorflag);
    C.addTransition(State);
    const MemRegion *reg = CD->getCXXThisVal().getAsRegion();
    State = State->remove<DtorMap>(reg);  
    C.addTransition(State);
    return;
  }

  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (Expr *Base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(Base)) {
        SVal CEV = State->getSVal(Base, LCtx);
        if(CEV != ThisSVal){
          unsigned Objectflag = State->get<ObjectFlag>();
          State = State->set<ObjectFlag>(--Objectflag);
          C.addTransition(State);
        }
      }
    }
  } 
}

// The function to check if a callexpr is a virtual function.
bool VirtualCallChecker::isVirtualCall(const CallExpr *CE) const {
  bool CallIsNonVirtual = false;

  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    // If the member access is fully qualified (i.e., X::F), then treat
    // this as a non-virtual call and do not warn.
    if (CME->getQualifier())
      CallIsNonVirtual = true;

    if (Expr *Base = CME->getBase()->IgnoreImpCasts()) {
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

// Get the symbolic value of the "this" object for a method call that created 
// the given stack frame. Returns None if the stack frame does not represent 
// a method call.
Optional<SVal>
VirtualCallChecker::getThisSVal(const StackFrameContext *SFC,const ProgramStateRef State) const {
  if (SFC->inTopFrame()) {
  const FunctionDecl *FD = SFC->getDecl()->getAsFunction();
    if (!FD)
      return None;
    const CXXMethodDecl *MD = dyn_cast_or_null<CXXMethodDecl>(FD->getParent());
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
    else if (const CXXConstructExpr *CCE = dyn_cast_or_null<CXXConstructExpr>(S))
      return State->getSVal(CCE, SFC->getParent());
    return None;
  }
}

// Check the base of the callexpr is equal to the this of the ctor
bool VirtualCallChecker::isCalledbyCtor(const CallExpr *CE,ProgramStateRef State,const LocationContext *LCtx) const {
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (Expr *Base = CME->getBase()->IgnoreImpCasts()){
      if (!isa<CXXThisExpr>(Base)) {
        SVal CEV = State->getSVal(Base, LCtx);
        CtorMapTy regmap = State->get<CtorMap>();
        for (CtorMapTy::iterator I = regmap.begin(),
                                 E = regmap.end();I != E; ++I) {
          const MemRegion *curreg = I->first;
          SVal curSV = State->getSVal(curreg);
          if (CEV == curSV)
            return true;
        }
      }
    }
  }
  return false;
}

// Check the base of the callexpr is equal to the this of the dtor
bool VirtualCallChecker::isCalledbyDtor(const CallExpr *CE,ProgramStateRef State,const LocationContext *LCtx) const {
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (Expr *Base = CME->getBase()->IgnoreImpCasts()){
      if (!isa<CXXThisExpr>(Base)) {
        SVal CEV = State->getSVal(Base, LCtx);
        DtorMapTy regmap = State->get<CtorMap>();
        for (DtorMapTy::iterator I = regmap.begin(),
                                 E = regmap.end();I != E; ++I) {
          const MemRegion *curreg = I->first;
          SVal curSV = State->getSVal(curreg);
          if (CEV == curSV)
            return true;
        }
      }
    }
  }
  return false;
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
  VirtualCallChecker *checker = mgr.registerChecker<VirtualCallChecker>();

  checker->isPureOnly = 
      mgr.getAnalyzerOptions().getBooleanOption("PureOnly", false,
                                                checker);
}
