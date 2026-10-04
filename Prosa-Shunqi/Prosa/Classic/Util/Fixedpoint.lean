-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/fixedpoint.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 16)

import Prosa.Classic.Util.Tactics
import Prosa.Classic.Util.Induction

/-!
Fixed-point iterations.

Representation notes:
* MathComp's `iter n f x` (`iter (S n) f x = f (iter n f x)`) is the Lean helper
  `iter` below, with the same recursion and argument order (Lean's `Nat.iterate`
  unfolds on the inside instead).
* A relation `rel T` is `T → T → Bool`; MathComp's `reflexive R` and `transitive R`
  are unfolded: `∀ x, R x x = true` and `∀ y x z, R x y = true → R y z = true → R x z
  = true` (MathComp's binder order).
* `iter_fixpoint_ind` has a `Type`-valued motive (`P : T -> Type`), so it is a Lean
  definition over `P : T → Sort w`.
* `x == y` is `decide (x = y)`; Boolean statements in proposition position are `… = true`.
-/

namespace Prosa.Classic.Util.Fixedpoint

universe u w

/-- LEAN_HELPER: MathComp's `iter n f x`. -/
def iter {T : Type u} : Nat → (T → T) → T → T
  | 0, _, x => x
  | n + 1, f, x => f (iter n f x)

theorem iter_fix (T : Type u) (F : T → T) (x : T) (k n : Nat) :
    iter k F x = iter (k + 1) F x → k ≤ n → iter n F x = iter (n + 1) F x := by
  intro e
  induction n with
  | zero =>
      intro h
      have : k = 0 := Nat.le_zero.mp h
      subst this
      exact e
  | succ n IH =>
      intro h
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · have IHe := IH (Nat.le_of_lt_succ hlt)
        show F (iter n F x) = F (F (iter n F x))
        exact congrArg F IHe
      · have : k = n + 1 := Nat.le_antisymm h hge
        subst this
        exact e

theorem fun_mon_iter_mon (f : Nat → Nat) (x0 x1 x2 : Nat) :
    x1 ≤ x2 → x0 ≤ f x0 → (∀ x3 x4, x3 ≤ x4 → f x3 ≤ f x4) →
    iter x1 f x0 ≤ iter x2 f x0 := by
  intro LE MIN MON
  have step : ∀ k, iter k f x0 ≤ iter (k + 1) f x0 := by
    intro k
    induction k with
    | zero => exact MIN
    | succ k ih => exact MON _ _ ih
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le LE
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (ih (Nat.le_add_right _ _)) (step _)

theorem fun_mon_iter_mon_helper (T : Type u) (f : T → T) (le : T → T → Bool) (x0 : T)
    (x1 : Nat) :
    (∀ x, le x x = true) →
    (∀ y x z, le x y = true → le y z = true → le x z = true) →
    (∀ x2 : Nat, le x0 (iter x2 f x0) = true) →
    (∀ x2 x3, le x0 x2 = true → le x2 x3 = true → le (f x2) (f x3) = true) →
    le (iter x1 f x0) (iter (x1 + 1) f x0) = true := by
  intro REFL TRANS MIN MON
  induction x1 with
  | zero => exact MIN 1
  | succ x1 ih => exact MON _ _ (MIN _) ih

theorem fun_mon_iter_mon_generic (T : Type u) (f : T → T) (le : T → T → Bool) (x0 : T)
    (x1 x2 : Nat) :
    (∀ x, le x x = true) →
    (∀ y x z, le x y = true → le y z = true → le x z = true) →
    x1 ≤ x2 →
    (∀ x3 x4, le x0 x3 = true → le x3 x4 = true → le (f x3) (f x4) = true) →
    (∀ x3 : Nat, le x0 (iter x3 f x0) = true) →
    le (iter x1 f x0) (iter x2 f x0) = true := by
  intro REFL TRANS LE MON MIN
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le LE
  induction d with
  | zero => exact REFL _
  | succ d ih =>
      exact TRANS _ _ _ (ih (Nat.le_add_right _ _))
        (fun_mon_iter_mon_helper T f le x0 (x1 + d) REFL TRANS MIN MON)

def monotone {T : Type u} (f : T → T) (R : T → T → Bool) : Prop :=
  ∀ x y, R x y = true → R (f x) (f y) = true

def iter_fixpoint {T : Type u} [DecidableEq T] (f : T → T) : Nat → T → Option T
  | 0, _ => none
  | step + 1, x => if decide (x = f x) then some x else iter_fixpoint f step (f x)

/-- LEAN_HELPER: one step of `iter_fixpoint` at a fixed point. -/
private theorem iter_fixpoint_succ_fix {T : Type u} [DecidableEq T] (f : T → T) (n : Nat) (x : T)
    (h : x = f x) : iter_fixpoint f (n + 1) x = some x := by
  simp only [iter_fixpoint, decide_eq_true h, ↓reduceIte]

/-- LEAN_HELPER: one step of `iter_fixpoint` away from a fixed point. -/
private theorem iter_fixpoint_succ_step {T : Type u} [DecidableEq T] (f : T → T) (n : Nat) (x : T)
    (h : ¬ x = f x) : iter_fixpoint f (n + 1) x = iter_fixpoint f n (f x) := by
  simp only [iter_fixpoint, decide_eq_false h, Bool.false_eq_true, ↓reduceIte]

theorem iter_fixpoint_cases {T : Type u} [DecidableEq T] (f : T → T) (max_steps : Nat) (x0 : T) :
    iter_fixpoint f max_steps x0 = none ∨
      ∃ y, iter_fixpoint f max_steps x0 = some y ∧ y = f y := by
  induction max_steps generalizing x0 with
  | zero => exact Or.inl rfl
  | succ n ih =>
      by_cases h : x0 = f x0
      · exact Or.inr ⟨x0, iter_fixpoint_succ_fix f n x0 h, h⟩
      · rw [iter_fixpoint_succ_step f n x0 h]
        exact ih (f x0)

def iter_fixpoint_ind {T : Type u} [DecidableEq T] (f : T → T) :
    (max_steps : Nat) → (x0 x : T) → iter_fixpoint f max_steps x0 = some x →
      (P : T → Sort w) → P x0 → (∀ x1, P x1 → P (f x1)) → P x
  | 0, _, _, SOME, _, _, _ => by simp [iter_fixpoint] at SOME
  | n + 1, x0, x, SOME, P, P0, ALL =>
      if h : x0 = f x0 then
        have hx : x0 = x := Option.some.inj ((iter_fixpoint_succ_fix f n x0 h).symm.trans SOME)
        hx ▸ P0
      else
        iter_fixpoint_ind f n (f x0) x ((iter_fixpoint_succ_step f n x0 h).symm.trans SOME) P
          (ALL x0 P0) ALL

theorem iter_fixpoint_ge_min {T : Type u} [DecidableEq T] (f : T → T) (R : T → T → Bool)
    (H_transitive : ∀ y x z, R x y = true → R y z = true → R x z = true)
    (H_monotone : monotone f R) :
    ∀ (max_steps : Nat) (x0 x1 x : T),
      iter_fixpoint f max_steps x1 = some x → R x0 x1 = true → R x1 (f x1) = true →
      R x0 x = true := by
  intro max_steps
  induction max_steps with
  | zero => intro x0 x1 x SOME; simp [iter_fixpoint] at SOME
  | succ n ih =>
      intro x0 x1 x SOME MIN BOT
      by_cases h : x1 = f x1
      · have hx : x1 = x := Option.some.inj ((iter_fixpoint_succ_fix f n x1 h).symm.trans SOME)
        rw [← hx]
        exact MIN
      · have SOME' : iter_fixpoint f n (f x1) = some x :=
          (iter_fixpoint_succ_step f n x1 h).symm.trans SOME
        exact ih x0 (f x1) x SOME' (H_transitive _ _ _ MIN BOT) (H_monotone _ _ BOT)

theorem iter_fixpoint_ge_bottom {T : Type u} [DecidableEq T] (f : T → T) (R : T → T → Bool)
    (H_reflexive : ∀ x, R x x = true)
    (H_transitive : ∀ y x z, R x y = true → R y z = true → R x z = true)
    (H_monotone : monotone f R) :
    ∀ (max_steps : Nat) (x0 x : T),
      iter_fixpoint f max_steps x0 = some x → R x0 (f x0) = true → R x0 x = true := by
  intro max_steps x0 x SOME BOT
  exact iter_fixpoint_ge_min f R H_transitive H_monotone max_steps x0 x0 x SOME (H_reflexive x0) BOT

end Prosa.Classic.Util.Fixedpoint
