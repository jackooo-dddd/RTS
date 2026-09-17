-- Translated from: ../rt-proofs/classic/util/fixedpoint.v
import Mathlib.Tactic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Defs.PartialOrder
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Fixedpoint

section FixedPoint

  lemma iter_fix (T : Type _) (F : T → T) (x : T) (k n : ℕ) :
      F^[k] x = F^[k + 1] x →
      k ≤ n →
      F^[n] x = F^[n + 1] x := by
    intro e hle
    induction n with
    | zero =>
      have hk0 : k = 0 := Nat.le_zero.mp hle
      subst hk0; exact e
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hle with hkn | hkn
      · subst hkn; exact e
      · have hle' : k ≤ n := Nat.lt_succ_iff.mp hkn
        have ihe := ih hle'
        show F^[n + 1] x = F^[n + 1 + 1] x
        rw [Function.iterate_succ', Function.comp]
        rw [show (n + 1 + 1) = (n + 1) + 1 from by omega]
        rw [Function.iterate_succ', Function.comp]
        rw [ihe]

  lemma fun_mon_iter_mon :
      ∀ (f : ℕ → ℕ) (x0 x1 x2 : ℕ),
        x1 ≤ x2 →
        f x0 ≥ x0 →
        (∀ x1 x2, x1 ≤ x2 → f x1 ≤ f x2) →
        f^[x1] x0 ≤ f^[x2] x0 := by
    intro f x0 x1 x2 LE MIN MON
    -- Helper: f^[d] x0 ≤ f^[d+1] x0 for all d
    have step : ∀ d, f^[d] x0 ≤ f^[d + 1] x0 := by
      intro d; induction d with
      | zero =>
        simp only [Function.iterate_zero, Nat.zero_add, Function.iterate_one]
        exact MIN
      | succ d' ihd =>
        have ihd' : f^[d'] x0 ≤ f (f^[d'] x0) := by
          rwa [Function.iterate_succ' f d', Function.comp] at ihd
        rw [Function.iterate_succ' f (d' + 1), Function.comp,
            Function.iterate_succ' f d', Function.comp]
        exact MON _ _ ihd'
    -- Main proof by induction on x1
    obtain ⟨delta, rfl⟩ := Nat.exists_eq_add_of_le LE
    clear LE
    induction x1 with
    | zero =>
      simp only [Function.iterate_zero, Nat.zero_add]
      induction delta with
      | zero => simp
      | succ d ihd =>
        exact le_trans ihd (step d)
    | succ n ih =>
      rw [Function.iterate_succ' f n, Function.comp,
          show n + 1 + delta = (n + delta) + 1 from by omega,
          Function.iterate_succ' f (n + delta), Function.comp]
      exact MON _ _ ih

  lemma fun_mon_iter_mon_helper :
      ∀ (T : Type _) (f : T → T) (le : T → T → Prop) (x0 : T) (x1 : ℕ),
        (∀ x, le x x) →
        (∀ x y z, le x y → le y z → le x z) →
        (∀ x2 : ℕ, le x0 (f^[x2] x0)) →
        (∀ x1 x2, le x0 x1 → le x1 x2 → le (f x1) (f x2)) →
        le (f^[x1] x0) (f^[x1 + 1] x0) := by
    intro T f le x0 x1 REFL TRANS MIN MON
    induction x1 with
    | zero =>
      simp only [Function.iterate_zero, Nat.zero_add, Function.iterate_one]
      exact MIN 1
    | succ n ih =>
      have ih' : le (f^[n] x0) (f (f^[n] x0)) := by
        have := ih
        rwa [Function.iterate_succ' f n, Function.comp] at this
      rw [show n + 1 + 1 = (n + 1) + 1 from by omega]
      rw [Function.iterate_succ' f (n + 1), Function.comp,
          Function.iterate_succ' f n, Function.comp]
      exact MON _ _ (MIN n) ih'

  lemma fun_mon_iter_mon_generic :
      ∀ (T : Type _) (f : T → T) (le : T → T → Prop) (x0 : T) (x1 x2 : ℕ),
        (∀ x, le x x) →
        (∀ x y z, le x y → le y z → le x z) →
        x1 ≤ x2 →
        (∀ x1 x2, le x0 x1 → le x1 x2 → le (f x1) (f x2)) →
        (∀ x2 : ℕ, le x0 (f^[x2] x0)) →
        le (f^[x1] x0) (f^[x2] x0) := by
    intro T f le x0 x1 x2 REFL TRANS LE MON MIN
    suffices h : ∀ delta, le (f^[x1] x0) (f^[x1 + delta] x0) by
      obtain ⟨delta, rfl⟩ := Nat.exists_eq_add_of_le LE
      exact h delta
    intro delta
    induction delta with
    | zero => simp; exact REFL _
    | succ d ih =>
      apply TRANS (f^[x1] x0) (f^[x1 + d] x0) (f^[x1 + (d + 1)] x0) ih
      rw [show x1 + (d + 1) = (x1 + d) + 1 from by omega]
      exact fun_mon_iter_mon_helper T f le x0 (x1 + d) REFL TRANS MIN MON

end FixedPoint

section Relations

  variable {T : Type _}
  variable (R : T → T → Prop)
  variable (f : T → T)

  def monotone (R : T → T → Prop) : Prop :=
    ∀ x y, R x y → R (f x) (f y)

end Relations

section Iteration

  variable {T : Type _} [DecidableEq T]
  variable (f : T → T)

  def iter_fixpoint : ℕ → T → Option T
    | 0, _ => none
    | n + 1, x =>
      let x' := f x
      if x == x' then some x
      else iter_fixpoint n x'

  section BasicLemmas

    lemma iter_fixpoint_cases :
        ∀ (max_steps : ℕ) (x0 : T),
          iter_fixpoint f max_steps x0 = none ∨
          ∃ y,
            iter_fixpoint f max_steps x0 = some y ∧
            y = f y := by
      intro max_steps
      induction max_steps with
      | zero => intro x0; left; simp [iter_fixpoint]
      | succ n ih =>
        intro x0
        simp only [iter_fixpoint]
        by_cases h : x0 == f x0
        · right
          exact ⟨x0, by simp [h], beq_iff_eq.mp h⟩
        · simp [h]
          exact ih (f x0)

    lemma iter_fixpoint_ind :
        ∀ (max_steps : ℕ) (x0 x : T),
          iter_fixpoint f max_steps x0 = some x →
          ∀ P : T → Prop,
            P x0 →
            (∀ x, P x → P (f x)) →
            P x := by
      intro max_steps
      induction max_steps with
      | zero => intro x0 x h; simp [iter_fixpoint] at h
      | succ n ih =>
        intro x0 x SOME P P0 ALL
        simp only [iter_fixpoint] at SOME
        by_cases h : x0 == f x0
        · simp [h] at SOME
          subst SOME
          rw [beq_iff_eq.mp h]
          exact ALL x0 P0
        · simp [h] at SOME
          exact ih (f x0) x SOME P (ALL x0 P0) ALL

  end BasicLemmas

  section RelationLemmas

    variable (R : T → T → Prop)
    variable (H_reflexive : ∀ x, R x x)
    variable (H_transitive : ∀ x y z, R x y → R y z → R x z)
    variable (H_monotone : monotone f R)
    include H_reflexive H_transitive H_monotone

    lemma iter_fixpoint_ge_min :
        ∀ (max_steps : ℕ) (x0 x1 x : T),
          iter_fixpoint f max_steps x1 = some x →
          R x0 x1 →
          R x1 (f x1) →
          R x0 x := by
      intro max_steps
      induction max_steps with
      | zero => intro x0 x1 x h; simp [iter_fixpoint] at h
      | succ n ih =>
        intro x0 x1 x SOME MIN BOT
        simp only [iter_fixpoint] at SOME
        by_cases h : x1 == f x1
        · simp [h] at SOME
          subst SOME
          exact MIN
        · simp [h] at SOME
          apply ih x0 (f x1) x SOME
          · exact H_transitive x0 x1 (f x1) MIN BOT
          · exact H_monotone x1 (f x1) BOT

    lemma iter_fixpoint_ge_bottom :
        ∀ (max_steps : ℕ) (x0 x : T),
          iter_fixpoint f max_steps x0 = some x →
          R x0 (f x0) →
          R x0 x := by
      intro max_steps x0 x SOME BOT
      have h := @iter_fixpoint_ge_min T _ f R H_reflexive H_transitive H_monotone max_steps x0 x0 x SOME (H_reflexive x0) BOT
      exact h

  end RelationLemmas

end Iteration

end Prosa.Classic.Util.Fixedpoint
