import «Warmup».Basic
import Lean

namespace Bar

@[foobar]
def myDecl : 4 = 2 * 2 := by decide

end Bar

#showFoo

@[foobar]
def aa : 5 = 5 * 1 := by decide

@[foobar]
def bb : Nat := 10

#showFoo

def even (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

def odd (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k + 1

@[parity_decl]
theorem even_def { n : Nat } : even n ↔ ∃ k, n = 2 * k := Iff.rfl

theorem odd_def { n : Nat } : odd n ↔ ∃ k, n = 2 * k + 1 := Iff.rfl

#show_parity

theorem foo
  {a b c d w x y z : Nat}
  {h1 : even x ∧ odd y → odd y}
  {h2 : odd z ∨ ¬ odd z} : even n ↔ odd c ∧ (even d ∨ odd d) :=
  sorry
