import Warmup.Basic

import Lean.Elab.Tactic

def even (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

def odd (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k + 1

@[parity_decl]
theorem odd_def { n : Nat } : odd n ↔ ∃ k, n = 2 * k + 1 := Iff.rfl

@[parity_decl]
theorem even_def { n : Nat } : even n ↔ ∃ k, n = 2 * k := Iff.rfl

/- Attempt at `parity_tac` -/

elab "parity_tac_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    -- TODO: Also update the goal
    -- let goal <- Lean.Elab.Tactic.getMainGoal
    let ctx <- Lean.MonadLCtx.getLCtx
    let env <- Lean.MonadEnv.getEnv
    let parityExt := parityExtension.getState env
    let fvars := ctx.getFVarIds
    fvars.forM fun fvar => do
      -- Ignore the top-level thm declaration.
      if (<- fvar.getDecl).isAuxDecl then
        return
      else
        parityExt.forM fun thm => do
          let lhs := thm.lhs
          let rhs := thm.rhs
          let type <- fvar.getType
          let name <- fvar.getUserName
          let newType <- rewrite_occurrences lhs rhs type
          -- TODO: This just returns a new context, how do I actually use that to update the proof state?
          let _ := ctx.modifyLocalDecl fvar fun decl => decl.setType newType
          Lean.logInfo m!"thm: {thm.name}, decl: {name},\nold type: {type}, new type: {newType}"


theorem foo {a b : Nat} (h1 : even a ∧ odd b) : even a ∨ odd b := by
  parity_tac_1
  sorry
