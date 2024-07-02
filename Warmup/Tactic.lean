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
    let goal <- Lean.Elab.Tactic.getMainGoal
    let ctx <- Lean.MonadLCtx.getLCtx
    let env <- Lean.MonadEnv.getEnv
    let parityExt := parityExtension.getState env
    Lean.logInfo m!"{parityExt.size}"
    let fvars := ctx.getFVarIds
    fvars.forM fun fvar => do
      -- Ignore the top-level thm declaration.
      if (<- fvar.getDecl).isAuxDecl then
        Lean.logInfo m!"skipping"
        return
      else
        Lean.logInfo m!"hello"
        parityExt.forM fun thm => do
          let lhs := thm.lhs
          let rhs := thm.rhs
          let type <- fvar.getType
          let newType <- rewrite_occurrences lhs rhs type
          let newCtx := ctx.modifyLocalDecl fvar fun decl => decl.setType newType
          Lean.logInfo m!"old type: {type}, new type: {newType}"

theorem t (h1 : 1 = 1) : 1 = 1 := by
  parity_tac_1

theorem foo
  {a b c d w x y z : Nat}
  {h1 : even x ∧ odd y → odd y}
  {h2 : odd z ∨ ¬ odd z} : even n ↔ odd c ∧ (even d ∨ odd d) :=
  parity_tac_1
