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
  DefaultBool isPureOnly;
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;

private:
  bool isVirtualCall(const CallExpr *CE) const;
  Optional<SVal> getThisSVal(const StackFrameContext *SFC,
                             const ProgramStateRef State) const;
  class VirtualBugVisitor : public BugReporterVisitorImpl<VirtualBugVisitor> {
  private:
    const unsigned Flag;
    bool Found;

  public:
    VirtualBugVisitor(const unsigned Flag) : Flag(Flag), Found(false) {}
    void Profile(llvm::FoldingSetNodeID &ID) const override{
      static int x = 0;
      ID.AddPointer(&x);
      ID.AddPointer(&Flag);
    }
    std::shared_ptr<PathDiagnosticPiece> VisitNode(const ExplodedNode *N,
                                                   const ExplodedNode *PrevN,
                                                   BugReporterContext &BRC,
                                                   BugReport &BR) override;
  };
};
} // end anonymous namespace

// GDM (generic data map) to store two integers in the program state. 
// One integer for constructors, one integer for destructors.
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstructorFlag, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(DestructorFlag, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(ObjectFlag, unsigned)

std::shared_ptr<PathDiagnosticPiece>
VirtualCallChecker::VirtualBugVisitor::VisitNode(const ExplodedNode *N,
                                                 const ExplodedNode *PrevN,
                                                 BugReporterContext &BRC,
                                                 BugReport &BR) {
  // We need the last ctor/dtor which call the virtual function
  // The visitor walks the ExplodedGraph backwards.
  if (Found)
    return nullptr;

  ProgramStateRef state = N->getState();
  const unsigned ctorflag = state->get<ConstructorFlag>();
  const unsigned dtorflag = state->get<DestructorFlag>();
  const LocationContext* LCtx = N->getLocationContext();
  const CXXConstructorDecl *CD =
        dyn_cast<CXXConstructorDecl>(LCtx->getDecl());
  const CXXDestructorDecl *DD =
        dyn_cast<CXXDestructorDecl>(LCtx->getDecl());  
  if((!CD && !DD) || (ctorflag!=Flag && dtorflag!=Flag)) return nullptr;
  
  // Retrieve the associated statement.  
  const Stmt *S = PathDiagnosticLocation::getStmt(N); 
  if (!S)
    return nullptr;
  Found = true;

  // Get the name of the last ctor/dtor which called the virtual function
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
  const Decl *D = dyn_cast_or_null<Decl>(Call.getDecl());
  if (!D)
    return;

  ProgramStateRef state = C.getState();
  const unsigned ctorflag = state->get<ConstructorFlag>();
  const unsigned dtorflag = state->get<DestructorFlag>();

  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const CXXMethodDecl *MD = dyn_cast_or_null<CXXMethodDecl>(D);

  const LocationContext *LCtx = C.getLocationContext();
  const StackFrameContext *SFC = LCtx->getCurrentStackFrame();
  Optional<SVal> ThisSVal = getThisSVal(SFC,state);

  // Enter a constructor, increase the corresponding integer.
  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(++constructorflag);
    C.addTransition(state);
    return;
  }

  // Enter a Destructor, increase the corresponding integer.
  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(++destructorflag);
    C.addTransition(state);
    return;
  }

  // Check if a object is entered, if yes, increase the corresponding integer.
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (Expr *base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(base)) {
        SVal CEV = state->getSVal(base, LCtx);
        if(CEV != ThisSVal){
          unsigned objectflag = state->get<ObjectFlag>();
          state = state->set<ObjectFlag>(++objectflag);
          C.addTransition(state);
        }
      }
    }
  } 

  // First Check if a virtual method is called, then check the 
  // GDM of constructor and destructor. 
  if (isPureOnly && !MD->isPure()) return;

  if (isVirtualCall(CE) && ctorflag > 0 && state->get<ObjectFlag>() == 0) {
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
    Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(ctorflag));
    C.emitReport(std::move(Reporter));
    return;
  }

  if (isVirtualCall(CE) && dtorflag > 0 && state->get<ObjectFlag>() == 0) {
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
    Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>(dtorflag));
    C.emitReport(std::move(Reporter));
    return;
  }
}

// The PostCall callback, when leave a constructor or a destructor, 
// decrease the corresponding integer.
void VirtualCallChecker::checkPostCall(const CallEvent &Call, 
                                       CheckerContext &C) const {
  const Decl *D = dyn_cast_or_null<Decl>(Call.getDecl());
  if (!D)
    return;

  ProgramStateRef state = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LCtx = C.getLocationContext();
  const StackFrameContext *SFC = LCtx->getCurrentStackFrame();
  Optional<SVal> ThisSVal = getThisSVal(SFC,state);

  // Leave a constructor, decrease the corresponding integer.
  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(--constructorflag);
    C.addTransition(state);
    return;
  }

  // Leave a Destructor, decrease the corresponding integer.
  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(--destructorflag);
    C.addTransition(state);
    return;
  }

  // Leave the object, decrease the corresponding integer.
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (Expr *base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(base)) {
        SVal CEV = state->getSVal(base, LCtx);
        if(CEV != ThisSVal){
          unsigned objectflag = state->get<ObjectFlag>();
          state = state->set<ObjectFlag>(--objectflag);
          C.addTransition(state);
        }
      }
    }
  } 
}

// The function to check if a virtual function is called
bool VirtualCallChecker::isVirtualCall(const CallExpr *CE) const {
  bool callIsNonVirtual = false;

  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    // If the member access is fully qualified (i.e., X::F), then treat
    // this as a non-virtual call and do not warn.
    if (CME->getQualifier())
      callIsNonVirtual = true;

    if (Expr *base = CME->getBase()->IgnoreImpCasts()) {
      // The most derived class is marked final.
      if (base->getBestDynamicClassType()->hasAttr<FinalAttr>())
        callIsNonVirtual = true;
    }
  }

  const CXXMethodDecl *MD =
      dyn_cast_or_null<CXXMethodDecl>(CE->getDirectCallee());
  if (MD && MD->isVirtual() && !callIsNonVirtual && !MD->hasAttr<FinalAttr>() 
      && !MD->getParent()->hasAttr<FinalAttr>())
    return true;
  return false;
}

// Get the symbolic value of the "this" object for a method call that created
// the given stack frame. Returns None if the stack frame does not represent 
// a method call.
Optional<SVal>
VirtualCallChecker::getThisSVal(const StackFrameContext *SFC,
                                const ProgramStateRef state) const {
  if (SFC->inTopFrame()) {
  const FunctionDecl *FD = SFC->getDecl()->getAsFunction();
    if (!FD)
      return None;
    const CXXMethodDecl *MD = dyn_cast_or_null<CXXMethodDecl>(FD->getParent());
    if (!MD)
      return None;
    Loc ThisLoc = state->getStateManager().getSValBuilder().getCXXThis(MD, SFC);
    return state->getSVal(ThisLoc);
  } else {
    const Stmt *S = SFC->getCallSite();
    if (!S)
      return None;
    if (const CXXMemberCallExpr *MCE = dyn_cast_or_null<CXXMemberCallExpr>(S))
      return state->getSVal(MCE->getImplicitObjectArgument(), SFC->getParent());
    else if (const CXXConstructExpr *CCE = dyn_cast_or_null<CXXConstructExpr>(S))
      return state->getSVal(CCE, SFC->getParent());
    return None;
  }
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
  VirtualCallChecker *checker = mgr.registerChecker<VirtualCallChecker>();

  checker->isPureOnly = 
      mgr.getAnalyzerOptions().getBooleanOption("PureOnly", false,
                                                checker);
}
