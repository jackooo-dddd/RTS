-- Translated from: ../rt-proofs/util/step_function.v
import Mathlib.Tactic
import Prosa.Util.Tactics

namespace Prosa.Util.Step_function

namespace StepFunction

section Defs

  variable (f : ℕ → ℕ)

  def is_step_function :=
    ∀ t, f (t + 1) ≤ f t + 1

end Defs

section Lemmas

  variable (f : ℕ → ℕ)
  variable (H_step_function : is_step_function f)

  section ExistsIntermediateValue

    variable (x1 x2 : ℕ)
    variable (H_is_interval : x1 ≤ x2)

    variable (y : ℕ)
    variable (H_between : f x1 ≤ y ∧ y < f x2)

    include H_step_function H_is_interval H_between

    theorem exists_intermediate_point :
        ∃ x_mid, x1 ≤ x_mid ∧ x_mid < x2 ∧ f x_mid = y := by
      -- Induct on delta = x2 - x1
      suffices h : ∀ delta, f x1 ≤ y ∧ y < f (x1 + delta) →
          ∃ x_mid, x1 ≤ x_mid ∧ x_mid < x1 + delta ∧ f x_mid = y by
        obtain ⟨hle, hlt⟩ := H_between
        have := h (x2 - x1) ⟨hle, by rwa [Nat.add_sub_cancel' H_is_interval]⟩
        obtain ⟨x_mid, h1, h2, h3⟩ := this
        exact ⟨x_mid, h1, by omega, h3⟩
      intro delta
      induction delta with
      | zero =>
        simp only [Nat.add_zero]
        intro ⟨hle, hlt⟩
        omega
      | succ n ih =>
        intro ⟨hge, hlt⟩
        have hstep := H_step_function (x1 + n)
        -- hstep : f (x1 + n + 1) ≤ f (x1 + n) + 1
        -- hlt : y < f (x1 + (n + 1))
        -- So f (x1 + n + 1) = f (x1 + (n+1))
        have heq : x1 + n + 1 = x1 + (n + 1) := by omega
        rw [heq] at hstep
        -- We need: y ≤ f (x1 + n)
        by_cases hle : y ≤ f (x1 + n)
        · -- Case: y ≤ f (x1 + n)
          by_cases heqy : f (x1 + n) = y
          · -- f (x1 + n) = y, so x_mid = x1 + n
            exact ⟨x1 + n, Nat.le_add_right x1 n, by omega, heqy⟩
          · -- y < f (x1 + n)
            have hlt' : y < f (x1 + n) := by omega
            obtain ⟨x_mid, h1, h2, h3⟩ := ih ⟨hge, hlt'⟩
            exact ⟨x_mid, h1, by omega, h3⟩
        · -- Case: f (x1 + n) < y, contradiction with step function and hlt
          push_neg at hle
          -- hle : f (x1 + n) < y
          -- hstep : f (x1 + (n+1)) ≤ f (x1 + n) + 1
          -- hlt : y < f (x1 + (n+1))
          omega

  end ExistsIntermediateValue

end Lemmas

section ExistsIntermediateValuePredicates

  variable (P : ℕ → Bool)

  variable (t1 t2 : ℕ)
  variable (H_t1_le_t2 : t1 ≤ t2)

  variable (H_not_P_at_t1 : ¬ (P t1 = true))

  variable (H_P_at_t2 : P t2 = true)

  include H_t1_le_t2 H_not_P_at_t1 H_P_at_t2

  theorem exists_first_intermediate_point :
      ∃ t, (t1 < t ∧ t ≤ t2) ∧ (∀ x, t1 ≤ x ∧ x < t → ¬ (P x = true)) ∧ P t = true := by
    -- First establish that t1 < t2
    have ht1_lt_t2 : t1 < t2 := by
      rcases Nat.eq_or_lt_of_le H_t1_le_t2 with h | h
      · exfalso; subst h; exact H_not_P_at_t1 H_P_at_t2
      · exact h
    -- Find the minimum n such that P (t1 + 1 + n) = true ∧ t1 + 1 + n ≤ t2
    have hex : ∃ n, P (t1 + 1 + n) = true ∧ t1 + 1 + n ≤ t2 := by
      refine ⟨t2 - (t1 + 1), ?_⟩
      constructor
      · have : t1 + 1 + (t2 - (t1 + 1)) = t2 := by omega
        rw [this]; exact H_P_at_t2
      · omega
    set m := Nat.find hex with hm_def
    have hfind := Nat.find_spec hex
    refine ⟨t1 + 1 + m, ?_, ?_, hfind.1⟩
    · exact ⟨by omega, hfind.2⟩
    · intro x ⟨hx1, hx2⟩
      by_cases hx_ge : x ≥ t1 + 1
      · -- x ≥ t1 + 1, so x - (t1 + 1) < m
        have hlt : x - (t1 + 1) < m := by omega
        have hmin := Nat.find_min hex hlt
        intro hPx
        apply hmin
        constructor
        · have : t1 + 1 + (x - (t1 + 1)) = x := by omega
          rw [this]; exact hPx
        · omega
      · -- x < t1 + 1, combined with x ≥ t1, so x = t1
        push_neg at hx_ge
        have : x = t1 := by omega
        subst this
        exact H_not_P_at_t1

end ExistsIntermediateValuePredicates

end StepFunction

end Prosa.Util.Step_function
