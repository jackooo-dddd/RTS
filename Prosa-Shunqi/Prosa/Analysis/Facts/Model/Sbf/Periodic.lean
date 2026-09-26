-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/sbf/periodic.v

import Prosa.Model.Priority.Classes
import Prosa.Model.Processor.Supply
import Prosa.Model.Processor.PlatformProperties
import Prosa.Analysis.Definitions.Sbf.Plain
import Prosa.Analysis.Definitions.Sbf.Periodic

namespace Prosa.Analysis.Facts.Model.Sbf.Periodic

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.Sbf.Plain
open Prosa.Analysis.Definitions.Sbf.Periodic

/-- `omega` after unfolding the time/work aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-! Representation notes: the binders `Π γ` are named `period alloc` (`Π` is
a reserved Lean token); `a < b` / `a <= b` hypotheses are the Nat orders. The
source's section-local `prm_sbf_valid_aux_11` is not public and is inlined
into the private pigeonhole lemma below. -/

section Helpers

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}

private theorem supply_during_split (sched : schedule PState) {a b c : instant}
    (hab : a ≤ b) (hbc : b ≤ c) :
    supply_during sched a c = supply_during sched a b + supply_during sched b c := by
  unfold supply_during
  exact (Finset.sum_Ico_consecutive _ hab hbc).symm

private theorem supply_during_le_length (hunit : unit_supply_proc_model PState)
    (sched : schedule PState) (a b : instant) : supply_during sched a b ≤ b - a := by
  unfold supply_during
  calc ∑ t ∈ Finset.Ico a b, supply_at sched t ≤ ∑ _t ∈ Finset.Ico a b, 1 :=
        Finset.sum_le_sum (fun t _ => hunit (sched t))
    _ = b - a := by simp

/-- Pigeonhole inside one period: a subinterval `[a, b)` of the `k`-th period
receives at least `(b - a) - (period - alloc)` supply. -/
private theorem supply_in_period (hunit : unit_supply_proc_model PState)
    (sched : schedule PState) (period alloc : duration)
    (hprm : periodic_resource_model period alloc sched) (k : Nat) (a b : instant)
    (hka : k * period ≤ a) (hab : a ≤ b) (hb : b ≤ (k + 1) * period) :
    b - a - (period - alloc) ≤ supply_during sched a b := by
  obtain ⟨_, hle, hsup⟩ := hprm
  have hk := hsup k
  have e1 : period * k = k * period := Nat.mul_comm _ _
  have e2 : period * (k + 1) = k * period + period := by
    rw [Nat.mul_comm, Nat.succ_mul]
  rw [e1, e2] at hk
  have e3 : (k + 1) * period = k * period + period := Nat.succ_mul _ _
  rw [e3] at hb
  rw [supply_during_split sched hka (Nat.le_trans hab hb),
    supply_during_split sched hab hb] at hk
  have h1 := supply_during_le_length hunit sched (k * period) a
  have h2 := supply_during_le_length hunit sched b (k * period + period)
  omega'

private theorem supply_full_periods (sched : schedule PState) (period alloc : duration)
    (hprm : periodic_resource_model period alloc sched) (m : Nat) :
    ∀ n : Nat, n * alloc ≤ supply_during sched (m * period) ((m + n) * period) := by
  obtain ⟨_, _, hsup⟩ := hprm
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hk := hsup (m + n)
      have e1 : period * (m + n) = (m + n) * period := Nat.mul_comm _ _
      have e2 : period * (m + n + 1) = (m + n) * period + period := by
        rw [Nat.mul_comm, Nat.succ_mul]
      rw [e1, e2] at hk
      have e3 : (m + (n + 1)) * period = (m + n) * period + period := by
        rw [← Nat.add_assoc, Nat.succ_mul]
      rw [e3, supply_during_split sched (Nat.mul_le_mul_right _ (Nat.le_add_right m n))
        (Nat.le_add_right _ _), Nat.succ_mul]
      omega'

end Helpers

/-- One-step growth facts for `prm_sbf`: either the full-period count is
unchanged, or it increases by one exactly at a period boundary. -/
private theorem prm_sbf_step (period alloc δ : duration) (hpos : 0 < period)
    (hle : alloc ≤ period) :
    prm_sbf period alloc δ ≤ prm_sbf period alloc (δ + 1) ∧
      prm_sbf period alloc (δ + 1) ≤ prm_sbf period alloc δ + 1 := by
  dsimp only [prm_sbf]
  by_cases hδ : period - alloc ≤ δ
  · have hs : δ + 1 - (period - alloc) = (δ - (period - alloc)) + 1 := by omega'
    rw [hs, Nat.succ_div]
    set x := δ - (period - alloc) with hx
    set n := x / period with hn
    have hdm := Nat.div_add_mod x period
    have hml := Nat.mod_lt x hpos
    rw [← hn] at hdm
    have hcomm : n * period = period * n := Nat.mul_comm _ _
    by_cases hd : period ∣ x + 1
    · rw [if_pos hd, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
      have hdm1 := Nat.div_add_mod (x + 1) period
      rw [Nat.mod_eq_zero_of_dvd hd, Nat.succ_div, if_pos hd, ← hn, Nat.mul_add,
        Nat.mul_one] at hdm1
      constructor <;> omega'
    · rw [if_neg hd, Nat.add_zero]
      constructor <;> omega'
  · have h0 : δ - (period - alloc) = 0 := by omega'
    rw [h0, Nat.zero_div, Nat.zero_mul, Nat.zero_mul]
    by_cases h1 : δ + 1 - (period - alloc) = 0
    · rw [h1, Nat.zero_div, Nat.zero_mul, Nat.zero_mul]
      omega'
    · have h1' : δ + 1 - (period - alloc) = 1 := by omega'
      rw [h1']
      rcases Nat.lt_or_ge 1 period with hp | hp
      · rw [Nat.div_eq_of_lt hp, Nat.zero_mul, Nat.zero_mul]
        omega'
      · have : period = 1 := by omega'
        subst this
        simp only [Nat.div_one, Nat.one_mul]
        omega'

theorem prm_sbf_monotone {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (period alloc : duration) :
    periodic_resource_model period alloc sched → sbf_is_monotone (prm_sbf period alloc) := by
  intro hprm x y hxy
  obtain ⟨hpos, hle, _⟩ := hprm
  have hxy' := of_decide_eq_true hxy
  clear hxy
  apply decide_eq_true
  induction y, hxy' using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ y _ ih => exact Nat.le_trans ih (prm_sbf_step period alloc y hpos hle).1

theorem prm_sbf_unit {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (period alloc : duration) :
    periodic_resource_model period alloc sched →
      unit_supply_bound_function (prm_sbf period alloc) := by
  intro hprm δ
  obtain ⟨hpos, hle, _⟩ := hprm
  exact (prm_sbf_step period alloc δ hpos hle).2

theorem prm_sbf_valid_aux_1 {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (hunit : unit_supply_proc_model PState) (sched : schedule PState) (period alloc : duration)
    (hprm : periodic_resource_model period alloc sched) (k : Nat) (q1 q2 : duration)
    (hq1 : q1 < period) (hq2 : q2 < period) :
    prm_sbf period alloc (k * period + q2 - (k * period + q1)) ≤
      supply_during sched (k * period + q1) (k * period + q2) := by
  have hd : k * period + q2 - (k * period + q1) = q2 - q1 := by omega'
  rw [hd]
  have hdiv : (q2 - q1 - (period - alloc)) / period = 0 := Nat.div_eq_of_lt (by omega')
  have hsbf : prm_sbf period alloc (q2 - q1) = q2 - q1 - 2 * (period - alloc) := by
    dsimp only [prm_sbf]
    rw [hdiv, Nat.zero_mul, Nat.zero_mul, Nat.zero_add, Nat.sub_zero]
  rw [hsbf]
  by_cases h12 : q1 ≤ q2
  · have hp := supply_in_period hunit sched period alloc hprm k (k * period + q1)
      (k * period + q2) (by omega') (by omega') (by rw [Nat.succ_mul]; omega')
    omega'
  · omega'

theorem prm_sbf_valid_aux_21 {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (period : duration) (k1 k2 : Nat) (q1 q2 : duration)
    (hq1 : q1 < period) (_hq2 : q2 < period) (hk : k1 < k2) :
    supply_during sched (k1 * period + q1) (k2 * period + q2) =
      supply_during sched (k1 * period + q1) ((k1 + 1) * period) +
        supply_during sched ((k1 + 1) * period) (k2 * period) +
          supply_during sched (k2 * period) (k2 * period + q2) := by
  have e1 : (k1 + 1) * period = k1 * period + period := Nat.succ_mul _ _
  have hk2 : (k1 + 1) * period ≤ k2 * period := Nat.mul_le_mul_right _ hk
  rw [supply_during_split sched (a := k1 * period + q1) (b := (k1 + 1) * period)
      (by omega') (by omega'),
    supply_during_split sched (a := (k1 + 1) * period) (b := k2 * period) hk2 (by omega')]
  omega'

theorem prm_sbf_valid_aux_22 {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (hunit : unit_supply_proc_model PState) (sched : schedule PState) (period alloc : duration)
    (hprm : periodic_resource_model period alloc sched) (k1 k2 : Nat) (q1 q2 : duration)
    (hq1 : q1 < period) (_hq2 : q2 < period) (_hk : k1 < k2) :
    period - q1 - (period - alloc) ≤ supply_during sched (k1 * period + q1) ((k1 + 1) * period) := by
  have e1 : (k1 + 1) * period = k1 * period + period := Nat.succ_mul _ _
  have hp := supply_in_period hunit sched period alloc hprm k1 (k1 * period + q1)
    ((k1 + 1) * period) (by omega') (by omega') (Nat.le_refl _)
  omega'

theorem prm_sbf_valid_aux_23 {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (period alloc : duration)
    (hprm : periodic_resource_model period alloc sched) (k1 k2 : Nat) (q1 q2 : duration)
    (_hq1 : q1 < period) (_hq2 : q2 < period) (hk : k1 < k2) :
    (k2 - (k1 + 1)) * alloc ≤ supply_during sched ((k1 + 1) * period) (k2 * period) := by
  have h := supply_full_periods sched period alloc hprm (k1 + 1) (k2 - (k1 + 1))
  rwa [show k1 + 1 + (k2 - (k1 + 1)) = k2 by omega'] at h

theorem prm_sbf_valid_aux_24 {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (hunit : unit_supply_proc_model PState) (sched : schedule PState) (period alloc : duration)
    (hprm : periodic_resource_model period alloc sched) (k1 k2 : Nat) (q1 q2 : duration)
    (_hq1 : q1 < period) (hq2 : q2 < period) (_hk : k1 < k2) :
    q2 - (period - alloc) ≤ supply_during sched (k2 * period) (k2 * period + q2) := by
  have hp := supply_in_period hunit sched period alloc hprm k2 (k2 * period)
    (k2 * period + q2) (Nat.le_refl _) (by omega') (by rw [Nat.succ_mul]; omega')
  omega'

theorem prm_sbf_valid_aux_2 {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (hunit : unit_supply_proc_model PState) (sched : schedule PState) (period alloc : duration)
    (hprm : periodic_resource_model period alloc sched) (k1 k2 : Nat) (q1 q2 : duration)
    (hq1 : q1 < period) (hq2 : q2 < period) (hk : k1 < k2) :
    prm_sbf period alloc (k2 * period + q2 - (k1 * period + q1)) ≤
      supply_during sched (k1 * period + q1) (k2 * period + q2) := by
  have S1 := prm_sbf_valid_aux_22 hunit sched period alloc hprm k1 k2 q1 q2 hq1 hq2 hk
  have S2 := prm_sbf_valid_aux_23 sched period alloc hprm k1 k2 q1 q2 hq1 hq2 hk
  have S3 := prm_sbf_valid_aux_24 hunit sched period alloc hprm k1 k2 q1 q2 hq1 hq2 hk
  rw [prm_sbf_valid_aux_21 sched period k1 k2 q1 q2 hq1 hq2 hk]
  obtain ⟨hpos, hle, _⟩ := hprm
  obtain ⟨m, rfl⟩ : ∃ m, k2 = k1 + 1 + m := ⟨k2 - (k1 + 1), by omega'⟩
  rw [show k1 + 1 + m - (k1 + 1) = m by omega'] at S2
  have eK2 : (k1 + 1 + m) * period = k1 * period + period + m * period := by
    rw [Nat.add_mul, Nat.succ_mul]
  have eK1 : (k1 + 1) * period = k1 * period + period := Nat.succ_mul _ _
  rw [eK2] at S2 S3 ⊢
  rw [eK1] at S1 S2 ⊢
  have hYX : m * alloc ≤ m * period := Nat.mul_le_mul_left _ hle
  have hΔ : k1 * period + period + m * period + q2 - (k1 * period + q1) =
      m * period + period + q2 - q1 := by omega'
  rw [hΔ]
  dsimp only [prm_sbf]
  set x := m * period + period + q2 - q1 - (period - alloc) with hx
  set n := x / period with hn
  have hdm := Nat.div_add_mod x period
  have hml := Nat.mod_lt x hpos
  rw [← hn] at hdm
  have hcomm : n * period = period * n := Nat.mul_comm _ _
  -- the full-period count is `m - 1`, `m` or `m + 1`
  have hup : n ≤ m + 1 := by
    by_contra h
    have : (m + 2) * period ≤ n * period := Nat.mul_le_mul_right _ (by omega')
    rw [show (m + 2) * period = m * period + period + period by
      rw [Nat.add_mul]; omega'] at this
    omega'
  have hlo : m ≤ n + 1 := by
    by_contra h
    have : (n + 2) * period ≤ m * period := Nat.mul_le_mul_right _ (by omega')
    rw [show (n + 2) * period = n * period + period + period by
      rw [Nat.add_mul]; omega'] at this
    omega'
  rcases (show n = m + 1 ∨ n = m ∨ n + 1 = m by omega') with h | h | h
  · have ea : n * alloc = m * alloc + alloc := by rw [h, Nat.succ_mul]
    have ep : n * period = m * period + period := by rw [h, Nat.succ_mul]
    rw [ea, ep]
    omega'
  · rw [h]
    omega'
  · have ea : m * alloc = n * alloc + alloc := by rw [← h, Nat.succ_mul]
    have ep : m * period = n * period + period := by rw [← h, Nat.succ_mul]
    omega'

theorem prm_sbf_valid {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (hunit : unit_supply_proc_model PState) (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (period alloc : duration) :
    periodic_resource_model period alloc sched →
      valid_supply_bound_function arr_seq sched (prm_sbf period alloc) := by
  intro hprm
  refine ⟨by simp [prm_sbf], ?_⟩
  intro j t1 t2 _ _ t ht
  have hpos := hprm.1
  have d1 := Nat.div_add_mod t1 period
  have d2 := Nat.div_add_mod t period
  have m1 := Nat.mod_lt t1 hpos
  have m2 := Nat.mod_lt t hpos
  rw [Nat.mul_comm] at d1 d2
  set k1 := t1 / period
  set k2 := t / period
  set q1 := t1 % period
  set q2 := t % period
  have hk : k1 ≤ k2 := by
    by_contra h
    have : (k2 + 1) * period ≤ k1 * period := Nat.mul_le_mul_right _ (by omega')
    rw [Nat.succ_mul] at this
    omega'
  rw [← d1, ← d2]
  rcases Nat.eq_or_lt_of_le hk with h | h
  · rw [h]
    exact prm_sbf_valid_aux_1 hunit sched period alloc hprm k2 q1 q2 m1 m2
  · exact prm_sbf_valid_aux_2 hunit sched period alloc hprm k1 k2 q1 q2 m1 m2 h

end Prosa.Analysis.Facts.Model.Sbf.Periodic
