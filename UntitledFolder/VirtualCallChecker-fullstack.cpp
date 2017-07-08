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
  bool isVirtualCall(const CallExpr *CE) const;
  int isCtorDtor(const LocationContext *LCt) const;
  mutable std::unique_ptr<BugType> BT_CT;
  mutable std::unique_ptr<BugType> BT_DT;

public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
};
}

void VirtualCallChecker::checkPreCall(const CallEvent &Call, 
                                      CheckerContext &C) const {

  const Decl *D = dyn_cast_or_null<Decl>(Call.getDecl());
  if (!D)
    return;

  const LocationContext* LCtx = C.getLocationContext();

  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  if(!CE)
    return;

  // First Check if a virtual method is called, then check the 
  // GDM of constructor and destructor. 
  if (isVirtualCall(CE) && isCtorDtor(LCtx)==1) {
    if (!BT_CT) {
      BT_CT.reset(new BugType(this, "Virtual call in constructor", "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
  }

  if (isVirtualCall(CE) && isCtorDtor(LCtx)==2) {
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
      if (!isa<CXXThisExpr>(base))
        return false;

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

int VirtualCallChecker::isCtorDtor(const LocationContext *LCt) const {
  int flag = 0;
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
      //if (CME->getQualifier())
       // return true;
      if (Expr *base = CME->getBase()->IgnoreImpCasts()) {
        if (!isa<CXXThisExpr>(base))
          ++flag;
      }
    }
   }
  }
  return 0;
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
	mgr.registerChecker<VirtualCallChecker>();
}
