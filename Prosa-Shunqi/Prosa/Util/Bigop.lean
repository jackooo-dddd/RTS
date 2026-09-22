-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/bigop.v

import Mathlib.Data.List.Basic

namespace Prosa.Util.Bigop

universe u v

/-!
`Monoid.law` in the source bundles an operation with associativity and
two-sided identity laws.  The translated theorem exposes the operation and
the same three laws explicitly.  This is an unbundling of the source
interface, not an added commutativity assumption.
-/

/--
Lean-side representation helper for MathComp's filtered sequence big
operator.  It is deliberately a right fold in source order, so it also
represents non-commutative monoids.
-/
def bigSeq {R : Type u} {X : Type v} (idx : R) (op : R → R → R)
    (P : X → Bool) (F : X → R) : List X → R
  | [] => idx
  | x :: xs => if P x then op (F x) (bigSeq idx op P F xs)
               else bigSeq idx op P F xs

/-- A predicate that is false everywhere leaves the big operator at its identity. -/
private theorem bigSeq_eq_identity_of_false
    {R : Type u} {X : Type v} (idx : R) (op : R → R → R)
    (P : X → Bool) (F : X → R) (xs : List X)
    (hP : ∀ x, x ∈ xs → P x = false) :
    bigSeq idx op P F xs = idx := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [bigSeq, hP x (by simp)]
      exact ih (fun y hy => hP y (by simp [hy]))

/--
A filtered big operator over a duplicate-free sequence and a singleton
predicate contains exactly the selected term.
-/
theorem big_pred1_seq
    {R : Type u} {idx : R} {op : R → R → R}
    (_opAssoc : ∀ x y z, op x (op y z) = op (op x y) z)
    (_opLeftId : ∀ x, op idx x = x)
    (opRightId : ∀ x, op x idx = x)
    {X : Type v} [DecidableEq X] {P : X → Bool} {F : X → R}
    (xs : List X) (i : X)
    (hi : i ∈ xs)
    (huniq : xs.Nodup)
    (hP : ∀ x, P x = decide (x = i)) :
    bigSeq idx op P F xs = F i := by
  induction xs with
  | nil => simp at hi
  | cons x xs ih =>
      rw [List.nodup_cons] at huniq
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · have hPi : P i = true := by simp [hP]
        have htail : bigSeq idx op P F xs = idx := by
          apply bigSeq_eq_identity_of_false
          intro y hy
          have hne : y ≠ i := by
            intro hyi
            subst y
            exact huniq.1 hy
          simp [hP, hne]
        simp [bigSeq, hPi, htail, opRightId]
      · have hne : x ≠ i := by
          intro hxi
          subst x
          exact huniq.1 hi
        have hPx : P x = false := by simp [hP, hne]
        rw [bigSeq, hPx]
        exact ih hi huniq.2

end Prosa.Util.Bigop
