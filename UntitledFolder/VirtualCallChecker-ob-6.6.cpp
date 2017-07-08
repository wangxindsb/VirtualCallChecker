#include "ClangSACheckers.h"
#include "clang/AST/DeclCXX.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"

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

private:
  class VirtualBugVisitor : public BugReporterVisitorImpl<VirtualBugVisitor> {
  public:
    void Profile(llvm::FoldingSetNodeID &ID) const override{
      static int x = 0;
      ID.AddPointer(&x);
    }
    std::shared_ptr<PathDiagnosticPiece> VisitNode(const ExplodedNode *N,
                                                   const ExplodedNode *PrevN,
                                                   BugReporterContext &BRC,
                                                   BugReport &BR) override;
  };
};
}

//GDM (generic data map) to store two integers in the program state. 
//One integer for constructors, one integer for destructors.
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
  ProgramStateRef State = N->getState();
  ProgramStateRef StatePrev = PrevN->getState();
  const unsigned ctorflag = State->get<ConstructorFlag>();
  const unsigned ctorflagPrev = StatePrev->get<ConstructorFlag>();

  if (ctorflag <= ctorflagPrev)
    return nullptr;
    
  const Stmt *S = PathDiagnosticLocation::getStmt(N); 
  if (!S)
    return nullptr;
    // Generate the extra diagnostic
  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return std::make_shared<PathDiagnosticEventPiece>(Pos, "called here");
}

  
void VirtualCallChecker::checkPreCall(const CallEvent &Call, 
                                      CheckerContext &C) const {

  const Decl *D = dyn_cast_or_null<Decl>(Call.getDecl());
  if (!D)
    return;

  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LC = C.getLocationContext();
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

  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    // If the member access is fully qualified (i.e., X::F), then treat
    // this as a non-virtual call and do not warn.
    if (const Expr *base = CME->getBase()->IgnoreImpCasts()) {
      SVal LOC = state->getSVal(base,LC);
      if (LOC.isValid()) {
      const Expr *MR = LOC.getAsSymbolicExpression();
        /*if(const SymbolicRegion *SMR = dyn_cast<SymbolicRegion>(MR)){
          if (auto S = dyn_cast<SymbolRegionValue>(SMR->getSymbol())) {*/
          if (!isa<CXXThisExpr>(MR)) {
            unsigned objectflag = state->get<ObjectFlag>();
            state = state->set<ObjectFlag>(++objectflag);
            C.addTransition(state);
            return;
          }
         
       }
       
    }
  } 

  // First Check if a virtual method is called, then check the 
  // GDM of constructor and destructor. 
  if (isVirtualCall(CE) && state->get<ConstructorFlag>() > 0 
      && state->get<ObjectFlag>() == 0) {
    if (!BT_CT) {
      BT_CT.reset(new BugType(this, "Call to virtual function during construction", 
                  "not pure"));
    }
    ExplodedNode *N = C.generateNonFatalErrorNode();
    auto Reporter = llvm::make_unique<BugReport>(*BT_CT, BT_CT->getName(), N);
    Reporter->addVisitor(llvm::make_unique<VirtualBugVisitor>());
    C.emitReport(std::move(Reporter));
    return;
  }

  if (isVirtualCall(CE) && state->get<DestructorFlag>() > 0 
      && state->get<ObjectFlag>() == 0) {
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
  const CallExpr *CE = dyn_cast_or_null<CallExpr>(Call.getOriginExpr());
  const LocationContext *LC = C.getLocationContext();
  ProgramStateRef state = C.getState();
  if (dyn_cast<CXXConstructorDecl>(D)) {
    unsigned constructorflag = state->get<ConstructorFlag>();
    state = state->set<ConstructorFlag>(--constructorflag);
    C.addTransition(state);
    return;
  }

  if (dyn_cast<CXXDestructorDecl>(D)) {
    unsigned destructorflag = state->get<DestructorFlag>();
    state = state->set<DestructorFlag>(--destructorflag);
    C.addTransition(state);
    return;
  }

  if (const MemberExpr *CME = dyn_cast<MemberExpr>(CE->getCallee())) {
    if (const Expr *base = CME->getBase()->IgnoreImpCasts()) {
      SVal LOC = state->getSVal(base,LC);
      if (LOC.isValid()) {
      const expr *MR = LOC.getAsSymbolicExpression();
      /*if(const SymbolicRegion *SMR = dyn_cast<SymbolicRegion>(MR)){
        if (auto S = dyn_cast<SymbolRegionValue>(SMR->getSymbol())) {*/
          if (!isa<CXXThisExpr>(MR)) {
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
      /*if (!isa<CXXThisExpr>(base))
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

void ento::registerVirtualCallChecker(CheckerManager &mgr) {
	mgr.registerChecker<VirtualCallChecker>();
}