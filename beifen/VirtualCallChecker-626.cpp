#include "ClangSACheckers.h"
#include "clang/AST/DeclCXX.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"

using namespace clang;
using namespace ento;

namespace {
class VirtualCallChecker: public Checker<check::PreCall, check::PostCall> {
  mutable std::unique_ptr<BugType> BT_CT;
  mutable std::unique_ptr<BugType> BT_DT;

public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;

private:
  bool isVirtualCall(const CallExpr *CE) const;
  bool isObject(const CallExpr *CE,ProgramStateRef state,const LocationContext *LCtx) const;
  bool isRealObject(const CallExpr *CE,ProgramStateRef state,const LocationContext *LCtx) const;
};
/*class SValWrapper {
  const SVal SV;
public :
  SValWrapper (const SVal &S) : SV(S) {}
  const SVal &get() const {return SV;}
  void Profile(llvm::FoldingSetNodeID &ID) const {
  ID.AddString (SV);
}
  bool operator ==(const SValWrapper &RHS ) const {return SV == RHS.SV;}
  bool operator <( const SValWrapper &RHS ) const {return SV < RHS.SV;}
};*/
}

//GDM (generic data map) to store two integers in the program state. 
//One integer for constructors, one integer for destructors.
REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstructorFlag, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(DestructorFlag, unsigned)
REGISTER_MAP_WITH_PROGRAMSTATE(CtorMap, const MemRegion*, unsigned)
REGISTER_TRAIT_WITH_PROGRAMSTATE(ObjectFlag, unsigned)
//REGISTER_LIST_WITH_PROGRAMSTATE(CtorMap, const MemRegion *)
//REGISTER_SET_WITH_PROGRAMSTATE(CtorMap, const MemRegion *)
//REGISTER_SET_WITH_PROGRAMSTATE(CtorMap, const MemRegion *)

void VirtualCallChecker::checkPreCall(const CallEvent &Call, 
                                      CheckerContext &C) const {

  const Decl *D = Call.getDecl();
  if (!D)
    return;

  const CXXConstructorCall *CC = dyn_cast_or_null<CXXConstructorCall>(&Call);
  ProgramStateRef state = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LCtx = C.getLocationContext();
  const StackFrameContext *SFC = LCtx->getCurrentStackFrame();

  // Enter a constructor, increase the corresponding integer
  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(++constructorflag);
    C.addTransition(state);
    //const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(D);
    //Loc ThisLoc = state->getStateManager().getSValBuilder().getCXXThis(MD, SFC);
    //SVal CV = CC->getCXXThisVal();
    if (!CC) return; 
    const MemRegion *reg = CC->getCXXThisVal().getAsRegion();
    state = state->set<CtorMap>(reg,1);
    //state = state->add<CtorMap>(reg);
    //state = state->set<CtorMap>(reg);
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

  if (isObject(CE,state,LCtx)) {
    unsigned Objectflag = state->get<ObjectFlag>();
    state = state->set<ObjectFlag>(++Objectflag);
    C.addTransition(state);
}

  // First Check if a virtual method is called, then check the 
  // GDM of constructor and destructor. 
  if (isVirtualCall(CE) && state->get<ConstructorFlag>() > 0 && (state->get<ObjectFlag>() == 0 || (state->get<ObjectFlag>() > 0 && isRealObject(CE,state,LCtx)))) {
    if (!BT_CT) {
      BT_CT.reset(new BugType(this, "Call to virtual function during construction", 
                  "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
    C.emitReport(std::move(Reporter));
    return;
  }

  if (isVirtualCall(CE) && state->get<DestructorFlag>() > 0) {
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

// The PostCall callback, when leave a constructor or a destructor, 
// decrease the corresponding integer
void VirtualCallChecker::checkPostCall(const CallEvent &Call, 
                                       CheckerContext &C) const {

  const Decl *D = Call.getDecl();
  if (!D)
    return;

  const auto *CC = dyn_cast_or_null<CXXConstructorCall>(&Call);
  ProgramStateRef state = C.getState();
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LCtx = C.getLocationContext();
  const StackFrameContext *SFC = LCtx->getCurrentStackFrame();

  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(--constructorflag);
    C.addTransition(state);
    //const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(D);
    //Loc ThisLoc = state->getStateManager().getSValBuilder().getCXXThis(MD, SFC);
    //SVal CV = state->getSVal(ThisLoc);
    const MemRegion *reg = CC->getCXXThisVal().getAsRegion();
    //CtorMapTy LS = state->get<CtorMap>();
    //SVal CV = CC->getCXXThisVal();
    state = state->remove<CtorMap>(reg);  
    //CtorMapTy LS = state->get<CtorMap>();
    //state = state->set<CtorMap>(LS.getTail());  
    C.addTransition(state);
    return;
  }

  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(--destructorflag);
    C.addTransition(state);
    return;
  }
  
  if (isObject(CE,state,LCtx)) {
    unsigned Objectflag = state->get<ObjectFlag>();
    state = state->set<ObjectFlag>(--Objectflag);
    C.addTransition(state); 
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
   //   if (!isa<CXXThisExpr>(base))
     //  return false;

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

bool VirtualCallChecker::isObject(const CallExpr *CE,ProgramStateRef state,const LocationContext *LCtx) const {
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
  if (Expr *base = CME->getBase()->IgnoreImpCasts()){
  if (!isa<CXXThisExpr>(base)) {
    SVal CEV = state->getSVal(base, LCtx);
    //const MemRegion* reg = CEV.getAsRegion();
   // if (!isa<CXXThisRegion>(reg))
     //  return true;
    //SVal S = state->getSVal(reg);
    //const MemRegion* curreg = S.getAsRegion();
    //auto RegionMap = state->get<CtorMap>();
    //if (!state->get<CtorMap>(reg))
    //CtorMapTy::iterator I = reg.getHead();
    //const MemRegion *curreg = reg.getHead();
    //SVal curSV = state->getSVal(curreg);
    //if (!state->contains<CtorMap>(reg))
    //const MemRegion* curreg = state->get<CtorMap>();
    CtorMapTy regmap = state->get<CtorMap>();
    if (regmap.isEmpty()) return true;
    for (CtorMapTy::iterator I = regmap.begin(),
                             E = regmap.end();I != E; ++I) {
      const MemRegion *curreg = I->first;
      SVal curSV = state->getSVal(curreg);
      if (CEV != curSV)
        return true;
    }
    }
    }
  }
  return false;
}

bool VirtualCallChecker::isRealObject(const CallExpr *CE,ProgramStateRef state,const LocationContext *LCtx) const {
  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
  if (Expr *base = CME->getBase()->IgnoreImpCasts()){
  if (!isa<CXXThisExpr>(base)) {
    SVal CEV = state->getSVal(base, LCtx);
    CtorMapTy regmap = state->get<CtorMap>();
    //if (regmap.isEmpty()) return false;
    for (CtorMapTy::iterator I = regmap.begin(),
                             E = regmap.end();I != E; ++I) {
      const MemRegion *curreg = I->first;
      SVal curSV = state->getSVal(curreg);
      if (CEV == curSV)
        return true;
    }
    }
    }
  }
  return false;
}

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
	mgr.registerChecker<VirtualCallChecker>();
}
