#include "ClangSACheckers.h"
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
  bool isVirtualCall(const CXXMethodDecl *MD) const;
  mutable std::unique_ptr<BugType> BT_CT;
  mutable std::unique_ptr<BugType> BT_DT;

public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
};
}

REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstructorFlag, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(DestructorFlag, unsigned)

void VirtualCallChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const {
  const Decl *D = Call.getDecl();
  ProgramStateRef state = C.getState();
  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(++constructorflag);
    C.addTransition(state);
    return;
  }

  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(++destructorflag);
    C.addTransition(state);
    return;
  }
    
  if (auto *MD = dyn_cast<CXXMethodDecl>(D)) {
    if (isVirtualCall(MD) && state->get<ConstructorFlag>()>0) {
      if (!BT_CT) {
        BT_CT.reset(new BugType(this, "Virtual call in constructor", "not pure"));
      }
      ExplodedNode *N = C.generateNonFatalErrorNode();
      auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
      C.emitReport(std::move(Reporter));
      return;
    }

    if (isVirtualCall(MD) && state->get<DestructorFlag>()>0) {
      if (!BT_DT) {
        BT_DT.reset(new BugType(this, "Virtual call in destructor", "not pure"));
      }
      ExplodedNode *N = C.generateNonFatalErrorNode();
      auto Reporter = llvm::make_unique<BugReport>(*BT_DT, BT_DT->getName(), N);
      C.emitReport(std::move(Reporter));
      return;
    }
  }
}

void VirtualCallChecker::checkPostCall(const CallEvent &Call, CheckerContext &C) const {
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
 
bool VirtualCallChecker::isVirtualCall(const CXXMethodDecl *MD) const {
  if (MD && MD->isVirtual() && !MD->hasAttr<FinalAttr>() &&
      !MD->getParent()->hasAttr<FinalAttr>())
    return true;
  return false;
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
	mgr.registerChecker<VirtualCallChecker>();
}
