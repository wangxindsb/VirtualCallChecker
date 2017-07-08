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
class VirtualCallChecker: public Checker<check::BeginFunction, check::EndFunction, check::PreCall> {
  mutable std::unique_ptr<BugType> BT_CT;
  mutable std::unique_ptr<BugType> BT_DT;

public:
  void checkBeginFunction(CheckerContext &C) const;
  void checkEndFunction(CheckerContext &C) const;
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
};
}

//GDM (generic data map) to store two integers in the program state. 
//One integer for constructors, one integer for destructors.
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstructorFlag, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(DestructorFlag, unsigned)
  
void VirtualCallChecker::checkBeginFunction(CheckerContext &C) const {
 // if (!C.inTopFrame())
   // return;
  const auto *LCtx = C.getLocationContext();
  const auto *MD = dyn_cast_or_null<CXXMethodDecl>(LCtx->getDecl());
  if (!MD)
    return;

  ProgramStateRef state = C.getState();

  // Enter a constructor, increase the corresponding integer
  if (isa<CXXConstructorDecl>(MD)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(++constructorflag);
    C.addTransition(state);
    return;
  }

  // Enter a Destructor, increase the corresponding integer
  if (isa<CXXDestructorDecl>(MD)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(++destructorflag);
    C.addTransition(state);
    return;
  }

 /* if (MD->isVirtual() && state->get<ConstructorFlag>() > 0) {
    if (!BT_CT) {
      BT_CT.reset(new BugType(this, "Call to virtual function during construction", 
                  "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
  }*/
}

// The PostCall callback, when leave a constructor or a destructor, 
// decrease the corresponding integer
void VirtualCallChecker::checkEndFunction(CheckerContext &C) const {
 // if (!C.inTopFrame())
   // return;
  const auto *LCtx = C.getLocationContext();
  const auto *MD = dyn_cast_or_null<CXXMethodDecl>(LCtx->getDecl());
  if (!MD)
    return;

  ProgramStateRef state = C.getState();
  if (dyn_cast<CXXConstructorDecl>(MD)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(--constructorflag);
    C.addTransition(state);
    return;
  }

  if (dyn_cast<CXXDestructorDecl>(MD)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(--destructorflag);
    C.addTransition(state);
    return;
  }
}

void VirtualCallChecker::checkPreCall(const CallEvent &Call, 
                                      CheckerContext &C) const {

  const auto *MD = dyn_cast_or_null<CXXMethodDecl>(Call.getDecl());
  if (!MD)
    return;

  ProgramStateRef state = C.getState();

  // Enter a constructor, increase the corresponding integer
  /*if (isa<CXXConstructorDecl>(MD)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(++constructorflag);
    C.addTransition(state);
    return;
  }

  // Enter a Destructor, increase the corresponding integer
  if (isa<CXXDestructorDecl>(MD)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(++destructorflag);
    C.addTransition(state);
    return;
  }*/

  // First Check if a virtual method is called, then check the 
  // GDM of constructor and destructor. 
  if (MD->isVirtual() && state->get<ConstructorFlag>() > 0) {
    if (!BT_CT) {
      BT_CT.reset(new BugType(this, "Call to virtual function during construction", 
                  "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
  }
  if (MD->isVirtual() && state->get<DestructorFlag>() > 0) {
    if (!BT_DT) {
      BT_DT.reset(new BugType(this, "Call to virtual function during destruction", 
                  "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_DT, BT_DT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
  }
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
	mgr.registerChecker<VirtualCallChecker>();
}
