import CaseStudies.Support.Common
import Mathlib.Data.List.Sort
import Prosa.Classic.Util.DivMod

/-!
Arithmetic of sporadic workload bounds: jobs whose arrival offsets (relative to the start of an
interval of length `t`) are pairwise at least `p` apart, each contributing at most `min e (t - x)`,
contribute at most `⌊t / p⌋ e + min e (t mod p)` in total.
-/

namespace CaseStudies.Support.WorkloadArith

open Prosa.Util.Sum (sumSeq)

/-- The no-carry-in workload bound `⌊t / p⌋ e + min e (t mod p)`. -/
def wnc (e p t : Nat) : Nat := t / p * e + min e (t % p)

theorem wnc_succ_le (e p t : Nat) (hp : 0 < p) : wnc e p t ≤ wnc e p (t + 1) := by
  unfold wnc
  rcases Nat.lt_or_ge (t % p + 1) p with h | h
  · have h1 : (t + 1) % p = t % p + 1 := by
      rw [Nat.add_mod, Nat.one_mod_eq_one.mpr (by omega), Nat.mod_eq_of_lt h]
    have h2 : (t + 1) / p = t / p := by
      have := Nat.div_add_mod t p
      have := Nat.div_add_mod (t + 1) p
      rw [h1] at this
      nlinarith [Nat.mul_le_mul_left p (Nat.le_refl ((t + 1) / p))]
    rw [h1, h2]
    exact Nat.add_le_add_left (min_le_min_left _ (Nat.le_succ _)) _
  · have hlt := Nat.mod_lt t hp
    have heq : t % p + 1 = p := by omega
    have h1 : (t + 1) % p = 0 := by
      have := Nat.div_add_mod t p
      have : t + 1 = (t / p + 1) * p := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
      rw [this, Nat.mul_mod_left]
    have h2 : (t + 1) / p = t / p + 1 := by
      have := Nat.div_add_mod t p
      have : t + 1 = (t / p + 1) * p := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
      rw [this, Nat.mul_div_cancel _ hp]
    rw [h1, h2, Nat.add_mul, Nat.one_mul]
    simp only [Nat.min_zero, Nat.add_zero]
    exact Nat.add_le_add_left (min_le_left _ _) _

theorem wnc_mono (e p : Nat) (hp : 0 < p) {t t' : Nat} (h : t ≤ t') : wnc e p t ≤ wnc e p t' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (wnc_succ_le e p _ hp)

theorem wnc_add_period (e p u : Nat) (hp : 0 < p) : wnc e p (u + p) = wnc e p u + e := by
  unfold wnc
  rw [Nat.add_mod_right, Nat.add_div_right _ hp, Nat.add_mul, Nat.one_mul]
  omega

/-- One job at offset `x` plus the bound for the window after `x + p` fits in the bound. -/
theorem min_add_wnc_le (e p t x : Nat) (hp : 0 < p) :
    min e (t - x) + wnc e p (t - x - p) ≤ wnc e p t := by
  refine le_trans ?_ (wnc_mono e p hp (Nat.sub_le t x))
  rcases Nat.lt_or_ge (t - x) p with h | h
  · have : t - x - p = 0 := by omega
    rw [this]
    unfold wnc
    rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    simp
  · have : t - x = (t - x - p) + p := by omega
    conv_rhs => rw [this, wnc_add_period e p _ hp]
    have := min_le_left e (t - x)
    omega

/-- Offsets sorted with gaps of at least `p`. -/
theorem sum_sorted_sep_le (e p : Nat) (hp : 0 < p) :
    ∀ (n : Nat) (A : List Nat), A.length = n → A.Pairwise (fun x y => x + p ≤ y) →
      ∀ t, sumSeq A (fun x => min e (t - x)) ≤ wnc e p t := by
  intro n
  induction n with
  | zero =>
    intro A hA _ t
    rw [List.length_eq_zero_iff] at hA; subst hA; simp [sumSeq]
  | succ n ih =>
    intro A hlen hA t
    cases A with
    | nil => simp at hlen
    | cons x A =>
      rw [List.pairwise_cons] at hA
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hshift : sumSeq A (fun y => min e (t - y)) =
          sumSeq (A.map (fun y => y - (x + p))) (fun y => min e ((t - x - p) - y)) := by
        unfold sumSeq
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro y hy
        have := hA.1 y hy
        simp only [Function.comp]
        congr 1
        omega
      have htail : (A.map (fun y => y - (x + p))).Pairwise (fun a b => a + p ≤ b) := by
        rw [List.pairwise_map]
        apply hA.2.imp_of_mem
        intro a b ha hb hab
        have := hA.1 a ha
        omega
      have ih' := ih _ (by simp [hlen]) htail (t - x - p)
      have hcons : sumSeq (x :: A) (fun y => min e (t - y)) =
          min e (t - x) + sumSeq A (fun y => min e (t - y)) := by
        unfold sumSeq; simp
      rw [hcons, hshift]
      exact le_trans (Nat.add_le_add_left ih' _) (min_add_wnc_le e p t x hp)

/-- Offsets in any order, pairwise at least `p` apart. -/
theorem sum_sep_le (e p : Nat) (hp : 0 < p) (A : List Nat)
    (hA : A.Pairwise (fun x y => x + p ≤ y ∨ y + p ≤ x)) (t : Nat) :
    sumSeq A (fun x => min e (t - x)) ≤ wnc e p t := by
  have hperm := List.mergeSort_perm A (fun x y => decide (x ≤ y))
  rw [← CaseStudies.Support.Common.sumSeq_perm _ hperm]
  apply sum_sorted_sep_le e p hp _ _ rfl _ t
  have hsorted := List.pairwise_mergeSort (le := fun x y => decide (x ≤ y))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) A
  have hsep := (hperm.pairwise_iff (fun {x y} h => by omega)).mpr hA
  exact (hsorted.and hsep).imp (fun ⟨h1, h2⟩ => by simp only [decide_eq_true_eq] at h1; omega)

end CaseStudies.Support.WorkloadArith

namespace CaseStudies.Support.WorkloadArith

open Prosa.Util.Sum (sumSeq)

/-- Offsets all at least `q`, pairwise at least `p` apart. -/
theorem sum_sep_shift_le (e p q : Nat) (hp : 0 < p) (A : List Nat) (hq : ∀ x ∈ A, q ≤ x)
    (hA : A.Pairwise (fun x y => x + p ≤ y ∨ y + p ≤ x)) (t : Nat) :
    sumSeq A (fun x => min e (t - x)) ≤ wnc e p (t - q) := by
  have hshift : sumSeq A (fun x => min e (t - x)) =
      sumSeq (A.map (fun x => x - q)) (fun x => min e ((t - q) - x)) := by
    unfold sumSeq
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro y hy
    have := hq y hy
    simp only [Function.comp]
    congr 1
    omega
  rw [hshift]
  apply sum_sep_le e p hp
  rw [List.pairwise_map]
  apply hA.imp_of_mem
  intro a b ha hb hab
  have := hq a ha
  have := hq b hb
  omega

/-- The carry-in workload bound of Guan et al. (RTSS 2009), as a function of `e`, `p`, `R`, `t`. -/
def wci09 (e p R t : Nat) : Nat :=
  min (e - 1) (t + R - e - (t - e) / p * p - p) + (t - e) / p * e + e

/-- A carry-in job that arrived `δ ∈ [1, R)` before the window and completes within `R`, followed by
jobs at least `p` apart, fits in `wci09`. -/
theorem ci09_arith (e p R δ : Nat) (he : 1 ≤ e) (heR : e ≤ R) (hRp : R ≤ p) (hδ1 : 1 ≤ δ)
    (hδR : δ < R) : ∀ t, min (e - 1) (R - δ) + wnc e p (t - (p - δ)) ≤ wci09 e p R t := by
  have hp : 0 < p := by omega
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.lt_or_ge t (e + p) with hlt | hge
    · have h0 : (t - e) / p = 0 := Nat.div_eq_of_lt (by omega)
      unfold wci09
      rw [h0]
      simp only [Nat.zero_mul, Nat.sub_zero]
      rcases Nat.lt_or_ge (t - (p - δ)) p with hu | hu
      · have : wnc e p (t - (p - δ)) = min e (t - (p - δ)) := by
          unfold wnc; rw [Nat.div_eq_of_lt hu, Nat.mod_eq_of_lt hu]; simp
        rw [this]
        omega
      · have hu2 : t - (p - δ) < 2 * p := by omega
        have h1 : (t - (p - δ)) / p = 1 := by
          have : t - (p - δ) = (t - (p - δ) - p) + p := by omega
          rw [this, Nat.add_div_right _ hp, Nat.div_eq_of_lt (by omega)]
        have h2 : (t - (p - δ)) % p = t - (p - δ) - p := by
          have := Nat.div_add_mod (t - (p - δ)) p
          rw [h1] at this; omega
        have : wnc e p (t - (p - δ)) = e + min e (t - (p - δ) - p) := by
          unfold wnc; rw [h1, h2]; simp
        rw [this]
        omega
    · have ih' := ih (t - p) (by omega)
      have hL : wnc e p (t - (p - δ)) ≤ wnc e p (t - p - (p - δ)) + e := by
        rw [← wnc_add_period e p _ hp]
        exact wnc_mono e p hp (by omega)
      have hR : wci09 e p R t = wci09 e p R (t - p) + e := by
        unfold wci09
        have hq : (t - e) / p = (t - p - e) / p + 1 := by
          have : t - e = (t - p - e) + p := by omega
          rw [this, Nat.add_div_right _ hp]
        rw [hq]
        have hmul := Nat.div_mul_le_self (t - p - e) p
        rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul]
        generalize (t - p - e) / p * p = A at hmul ⊢
        generalize (t - p - e) / p * e = B
        omega
      rw [hR]
      omega

end CaseStudies.Support.WorkloadArith

namespace CaseStudies.Support.WorkloadArith

theorem wnc_succ_le_add_one (e p t : Nat) (hp : 0 < p) (hep : e ≤ p) :
    wnc e p (t + 1) ≤ wnc e p t + 1 := by
  unfold wnc
  rcases Nat.lt_or_ge (t % p + 1) p with h | h
  · have h1 : (t + 1) % p = t % p + 1 := by
      rw [Nat.add_mod, Nat.one_mod_eq_one.mpr (by omega), Nat.mod_eq_of_lt h]
    have h2 : (t + 1) / p = t / p := by
      have := Nat.div_add_mod t p
      have := Nat.div_add_mod (t + 1) p
      rw [h1] at this
      nlinarith [Nat.mul_le_mul_left p (Nat.le_refl ((t + 1) / p))]
    rw [h1, h2]
    have := min_le_min_left e (Nat.le_succ (t % p))
    omega
  · have hlt := Nat.mod_lt t hp
    have heq : t % p + 1 = p := by omega
    have hdecomp : t + 1 = (t / p + 1) * p := by
      have := Nat.div_add_mod t p
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
    have h1 : (t + 1) % p = 0 := by rw [hdecomp, Nat.mul_mod_left]
    have h2 : (t + 1) / p = t / p + 1 := by rw [hdecomp, Nat.mul_div_cancel _ hp]
    rw [h1, h2, Nat.add_mul, Nat.one_mul]
    simp only [Nat.min_zero, Nat.add_zero]
    have : e ≤ min e (t % p) + 1 := by rw [Nat.min_def]; split <;> omega
    omega

theorem wnc_le_add (e p t : Nat) (hp : 0 < p) (hep : e ≤ p) :
    ∀ d, wnc e p (t + d) ≤ wnc e p t + d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have := wnc_succ_le_add_one e p (t + d) hp hep
    rw [← Nat.add_assoc]; omega

theorem div_ceil_spec (x d : Nat) (hd : 0 < d) :
    x ≤ Prosa.Classic.Util.DivMod.div_ceil x d * d ∧
      ∀ k, x ≤ k * d → Prosa.Classic.Util.DivMod.div_ceil x d ≤ k := by
  unfold Prosa.Classic.Util.DivMod.div_ceil
  have hdm := Nat.div_add_mod x d
  have hml := Nat.mod_lt x hd
  split
  · rename_i hdvd
    have hm : x % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
    refine ⟨by rw [Nat.mul_comm]; omega, fun k hk => ?_⟩
    by_contra hlt
    have : k * d < x / d * d := Nat.mul_lt_mul_of_pos_right (by omega) hd
    rw [Nat.mul_comm (x / d)] at this
    omega
  · rename_i hndvd
    have hm : x % d ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
    refine ⟨by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega, fun k hk => ?_⟩
    by_contra hlt
    have : k ≤ x / d := by omega
    have := Nat.mul_le_mul_right d this
    rw [Nat.mul_comm (x / d)] at this
    omega

end CaseStudies.Support.WorkloadArith
