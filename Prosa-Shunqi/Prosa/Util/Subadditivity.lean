-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/subadditivity.v

import Mathlib.Tactic

namespace Prosa.Util.Subadditivity

def subadditive_at (f : Nat → Nat) (h : Nat) : Prop :=
  ∀ a b, a + b = h → f h ≤ f a + f b

def subadditive_until (f : Nat → Nat) (h : Nat) : Prop :=
  ∀ x, x < h → subadditive_at f x

def subadditive (f : Nat → Nat) : Prop :=
  ∀ h, subadditive_at f h

def subadditive_standard (f : Nat → Nat) : Prop :=
  ∀ a b, f (a + b) ≤ f a + f b

theorem subadditive_standard_equivalence (f : Nat → Nat) :
    subadditive f ↔ subadditive_standard f := by
  constructor
  · intro h a b
    exact h (a + b) a b rfl
  · intro h point a b hab
    subst point
    exact h a b

theorem subadditive_leq_mul (f : Nat → Nat) (h_subadditive : subadditive f) :
    ∀ n m, 0 < m → f (m * n) ≤ m * f n := by
  intro n m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        f (Nat.succ (Nat.succ k) * n) = f (Nat.succ k * n + n) := by
          rw [Nat.succ_mul]
        _ ≤ f (Nat.succ k * n) + f n :=
          h_subadditive _ _ _ rfl
        _ ≤ Nat.succ k * f n + f n :=
          Nat.add_le_add_right (ih (Nat.succ_pos k)) _
        _ = Nat.succ (Nat.succ k) * f n :=
          (Nat.succ_mul (Nat.succ k) (f n)).symm

end Prosa.Util.Subadditivity
