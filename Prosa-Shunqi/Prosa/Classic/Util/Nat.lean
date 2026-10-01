-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/nat.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 10)

import Prosa.Util.Nat

/-!
Additional lemmas about natural numbers.  The source re-exports
`prosa.util.nat` (imported above).

Representation notes: Boolean equalities `(a == b)` in a Boolean equation are
`decide (a = b)`; `a != b` is `!decide (a = b)`; the `bool → nat` coercion is
`Bool.toNat`.
-/

namespace Prosa.Classic.Util.Nat

theorem subh1 :
    ∀ m n p : Nat,
      n ≤ m →
      m - n + p = m + p - n := by
  intro m n p h
  omega

theorem subh2 :
    ∀ m1 m2 n1 n2 : Nat,
      m2 ≤ m1 →
      n2 ≤ n1 →
      (m1 + n1) - (m2 + n2) = m1 - m2 + (n1 - n2) := by
  intro m1 m2 n1 n2 h1 h2
  omega

theorem addnb (b1 b2 : Bool) :
    (!decide (b1.toNat + b2.toNat = 0)) = (b1 || b2) := by
  cases b1 <;> cases b2 <;> rfl

theorem subh4 :
    ∀ m n p : Nat,
      m ≤ n →
      p ≤ n →
      decide (m = n - p) = decide (p = n - m) := by
  intro m n p h1 h2
  apply decide_eq_decide.mpr
  omega

theorem addmovr :
    ∀ m n p : Nat,
      n ≤ m →
      (m - n = p ↔ m = p + n) := by
  intro m n p h
  omega

theorem addmovl :
    ∀ m n p : Nat,
      n ≤ m →
      (p = m - n ↔ p + n = m) := by
  intro m n p h
  omega

theorem ltSnm : ∀ n m : Nat, n + 1 < m → n < m := by
  intro n m h
  omega

theorem min_lt_same :
    ∀ x y z : Nat,
      Nat.min x z < Nat.min y z → x < y := by
  intro x y z h
  simp only [Nat.min_def] at h
  split at h <;> split at h <;> omega

end Prosa.Classic.Util.Nat
