import Warmup.Basic

import Lean.Elab.Tactic

/- Examples -/

elab "custom_sorry" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal <- Lean.Elab.Tactic.getMainGoal
    let goalDecl <- goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type : {goalType}"
    Lean.Elab.admitGoal goal

example : 1 = 2 := by
  custom_sorry

elab "list_local_decls_3" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
      let eq? ← Lean.Meta.isExprDefEq declType goalType -- **NEW** Check if type equals goal type.
      Lean.logInfo m!"+ local decl[EQUAL? {eq?}]: name: {declName}, type: {declType}, aux: {decl.isAuxDecl}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_3
-- + local decl[EQUAL? false]: name: test_list_local_decls_3
-- + local decl[EQUAL? true]: name: H1
-- + local decl[EQUAL? false]: name: H2
  rfl

elab "custom_assump" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal <- Lean.Elab.Tactic.getMainGoal
    let goalType <- Lean.Elab.Tactic.getMainTarget
    let lctx <- Lean.MonadLCtx.getLCtx
    let matching_expr <- lctx.findDeclM? fun ldecl: Lean.LocalDecl => do
      let declExpr := ldecl.toExpr
      let declType <- Lean.Meta.inferType declExpr
      if (<- Lean.Meta.isExprDefEq declType goalType)
      then return some declExpr
      else return none
    match matching_expr with
    | some e => Lean.Elab.Tactic.closeMainGoal e
    | none   => Lean.Meta.throwTacticEx `custom_assump goal (m!"unable to find hypothesis of type {goalType}")


theorem try_custom_assump (h1 : 1 = 1) (h2 : 2 = 2) : 2 = 2 := by
  custom_assump

#check_failure (by custom_assump : (H1 : 1 = 1) → 2 = 2)

open Lean.Elab.Tactic in
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

theorem test_faq_have : True := by
  custom_let n : Nat := 5
  custom_let h : n = n := rfl
-- n : Nat := 5
-- h : n = n
-- ⊢ True
  trivial
