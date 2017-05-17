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
class VirtualCallChecker: public Checker<check::PreCall, check::PostCall> {
  bool isVirtualCall(const CallExpr *CE) const;
  mutable std::unique_ptr<BugType> BT_CT;
  mutable std::unique_ptr<BugType> BT_DT;

public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
};
}

//GDM (generic data map) to store two integers in the program state. 
//One integer for constructors, one integer for destructors.
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstructorFlag, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(DestructorFlag, unsigned)

void VirtualCallChecker::checkPreCall(const CallEvent &Call, 
                                      CheckerContext &C) const {

  const Decl *D = dyn_cast_or_null<Decl>(Call.getDecl());
  if (!D)
    return;

  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());

  ProgramStateRef state = C.getState();

  // Enter a constructor, increase the corresponding integer
  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(++constructorflag);
    C.addTransition(state);
    return;
  }

  // Enter a Destructor, increase the corresponding integer
  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(++destructorflag);
    C.addTransition(state);
    return;
  }

  // First Check if a virtual method is called, then check the 
  // GDM of constructor and destructor. 
  if (isVirtualCall(CE) && state->get<ConstructorFlag>() > 0) {
    if (!BT_CT) {
      BT_CT.reset(new BugType(this, "Virtual call in constructor", "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
  }

  if (isVirtualCall(CE) && state->get<DestructorFlag>() > 0) {
    if (!BT_DT) {
      BT_DT.reset(new BugType(this, "Virtual call in destructor", "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_DT, BT_DT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
  }
}

// The PreCall callback, when leave a constructor or a destructor, 
// decrease the corresponding integer
void VirtualCallChecker::checkPostCall(const CallEvent &Call, 
                                       CheckerContext &C) const {

  const Decl *D = Call.getDecl();
  ProgramStateRef state = C.getState();
  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(--constructorflag);
    return;
  }

  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(--destructorflag);
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

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
	mgr.registerChecker<VirtualCallChecker>();
}
