-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/setoid.v

import Mathlib.Data.Nat.Basic

namespace Prosa.Util.Setoid

/--
Boolean implication packaged as a relation.  This is the direct Lean
counterpart of the source inductive `leb`; Bool truth is represented
explicitly by equality with `true`.
-/
inductive leb (a b : Bool) : Prop
  | intro : (a = true → b = true) → leb a b

/-- `leb` is exactly implication between the truth interpretations. -/
theorem leb_eq (a b : Bool) : leb a b ↔ (a = true → b = true) := by
  constructor
  · intro h
    cases h with
    | intro hab => exact hab
  · exact leb.intro

/-! The source registers the following facts as Rocq setoid-rewriting
instances.  Lean's rewriting mechanism has a different interface, so these
are named representation helpers rather than competing global order
instances. -/

/-- Lean helper corresponding to reflexivity of the source rewrite relation. -/
theorem leb_refl (a : Bool) : leb a a := leb.intro id

/-- Lean helper corresponding to transitivity of the source rewrite relation. -/
theorem leb_trans {a b c : Bool} (hab : leb a b) (hbc : leb b c) : leb a c := by
  rw [leb_eq] at hab hbc ⊢
  exact fun ha => hbc (hab ha)

/-- Lean helper: Boolean conjunction is monotone for `leb`. -/
theorem leb_and {a b c d : Bool} (hab : leb a b) (hcd : leb c d) :
    leb (a && c) (b && d) := by
  rw [leb_eq] at hab hcd ⊢
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Lean helper: Boolean disjunction is monotone for `leb`. -/
theorem leb_or {a b c d : Bool} (hab : leb a b) (hcd : leb c d) :
    leb (a || c) (b || d) := by
  rw [leb_eq] at hab hcd ⊢
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/--
Turn the translated MathComp-order premise into Lean's proposition-valued
natural-number order.  Under the approved Nat/order representation this is
the identity proof function, mirroring the source use of `leP`.
-/
def leqRW {m n : Nat} (h : m ≤ n) : m ≤ n := h

end Prosa.Util.Setoid
