#include "ClangSACheckers.h"
#include "clang/AST/DeclCXX.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"

using namespace clang;
using namespace ento;

namespace {
class VirtualCallChecker: public Checker<check::PreCall> {
  mutable std::unique_ptr<BugType> BT_CT;
  mutable std::unique_ptr<BugType> BT_DT;

public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;

private:
  bool isVirtualCall(const CallExpr *CE) const;
  int isCtorDtor(const LocationContext* LCtx, 
                const CallExpr *CE, ProgramStateRef state) const;
  Optional<SVal> getThisSVal(const StackFrameContext *SFC,const ProgramStateRef state) const;
};
}

void VirtualCallChecker::checkPreCall(const CallEvent &Call, 
                                      CheckerContext &C) const {

  const Decl *D = dyn_cast_or_null<Decl>(Call.getDecl());
  if (!D)
    return;

  const LocationContext* LCtx = C.getLocationContext();
  ProgramStateRef state = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  if(!CE)
    return;

  // First Check if a virtual method is called, then check the 
  // GDM of constructor and destructor. 
  if (isVirtualCall(CE) && isCtorDtor(LCtx,CE,state)==1) {
    if (!BT_CT) {
      BT_CT.reset(new BugType(this, "Virtual call in constructor", "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
  }

  if (isVirtualCall(CE) && isCtorDtor(LCtx,CE,state)==2) {
    if (!BT_DT) {
      BT_DT.reset(new BugType(this, "Virtual call in destructor", "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_DT, BT_DT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
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
  /*    if (!isa<CXXThisExpr>(base))
        return false;*/

      // The most derived class is marked final.
      if (base->getBestDynamicClassType()->hasAttr<FinalAttr>())
        callIsNonVirtual = true;
    }
  }

  const CXXMethodDecl *MD =
      dyn_cast_or_null<CXXMethodDecl>(CE->getDirectCallee());
  if (MD && MD->isVirtual() && !callIsNonVirtual && !MD->hasAttr<FinalAttr>() &&
      !MD->getParent()->hasAttr<FinalAttr>())
    return true;
  return false;
}

// If the function is called during a ctor, return 1,
// else if it is called during a dtor, return 2, else return 0.
int VirtualCallChecker::isCtorDtor(const LocationContext *LCt,
                                   const CallExpr *CE, ProgramStateRef state) const {
  // The flag for object. If the function is called by an object, increase the flag. 
  int flag = 0;
  const StackFrameContext *SFC = LCt->getCurrentStackFrame();
  Optional<SVal> ThisSVal = getThisSVal(SFC,state);

  // The situation where a function is directly called by an object
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (Expr *base = CME->getBase()->IgnoreImpCasts()) {
      if (!isa<CXXThisExpr>(base)) {
        SVal CEV = state->getSVal(base, LCt);
        if(CEV != ThisSVal) ++flag;
      }
    }     
  }

  // The situation where a function is not directly called by an object
  // Use the stackframe to get the object which calls the function
  for (const LocationContext *LCtx = LCt; LCtx; LCtx = LCtx->getParent()) {
    if(const CXXMethodDecl *MD =
        dyn_cast_or_null<CXXMethodDecl>(LCtx->getDecl())){
    if(isa<CXXConstructorDecl>(MD) && (flag == 0))
      return 1;
    if(isa<CXXDestructorDecl>(MD) && (flag == 0)) 
      return 2;}
    const Stmt *CallSite = LCtx->getCurrentStackFrame()->getCallSite();
    if (const CallExpr *CE = dyn_cast_or_null<CallExpr>(CallSite)) {
      if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
        if (Expr *base = CME->getBase()->IgnoreImpCasts()) {
          if (!isa<CXXThisExpr>(base)) {
            SVal CEV = state->getSVal(base, LCtx);
            if(CEV != ThisSVal) ++flag;
          }
        }     
      }
    }
  }
  return 0;
}

// Get the symbolic value of the "this" object for a method call that created the given stack frame. 
// Returns None if the stack frame does not represent a method call.
Optional<SVal>
VirtualCallChecker::getThisSVal(const StackFrameContext *SFC,const ProgramStateRef state) const {
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
	mgr.registerChecker<VirtualCallChecker>();
}
