-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/behavior/supply.v

import Prosa.Model.Processor.PlatformProperties
import Prosa.Util.All

namespace Prosa.Analysis.Facts.Behavior.Supply

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Util.UnitGrowth
open scoped BigOperators

universe u v w

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (sched : schedule PState)

/-- Instantaneous service is bounded by total instantaneous supply. -/
theorem service_at_le_supply_at (j : Job) (t : instant) :
    service_at sched j t ≤ supply_at sched t := by
  unfold service_at supply_at ProcessorState.service_in ProcessorState.supply_in
  apply Finset.sum_le_sum
  intro c _
  exact PState.service_on_le_supply_on j (sched t) c

/-- Positive service implies positive supply. -/
theorem pos_service_impl_pos_supply (j : Job) (t : instant) :
    0 < service_at sched j t → 0 < supply_at sched t := by
  intro hservice
  exact lt_of_lt_of_le hservice (service_at_le_supply_at sched j t)

/-- At each instant there is either a blackout or positive supply. -/
theorem blackout_or_supply (t : instant) :
    is_blackout sched t = true ∨ has_supply sched t = true := by
  cases h : has_supply sched t with
  | false => exact Or.inl (by simp [is_blackout, h])
  | true => exact Or.inr rfl

section UnitSupply

variable (hunit : unit_supply_proc_model PState)

/-- Unit supply is the complement of the blackout indicator. -/
theorem supply_at_complement (hunit : unit_supply_proc_model PState)
    (t : instant) :
    supply_at sched t = 1 - (is_blackout sched t).toNat := by
  have hle : supply_at sched t ≤ 1 := by
    simpa [supply_at] using hunit (sched t)
  cases hs : supply_at sched t with
  | zero => simp [is_blackout, has_supply, hs]
  | succ n =>
      rw [hs] at hle
      have hge : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
      have hn : n = 0 := Nat.succ.inj (Nat.le_antisymm hle hge)
      subst n
      simp [is_blackout, has_supply, hs]

/-- The blackout indicator is the complement of unit supply. -/
theorem is_blackout_complement (hunit : unit_supply_proc_model PState)
    (t : instant) :
    (is_blackout sched t).toNat = 1 - supply_at sched t := by
  have h := supply_at_complement sched hunit t
  cases hb : is_blackout sched t with
  | false =>
      have ha : supply_at sched t = 1 := by simpa [hb] using h
      simp [ha]
  | true =>
      have ha : supply_at sched t = 0 := by simpa [hb] using h
      simp [ha]

/-- Instantaneous supply is at most one. -/
theorem supply_at_le_1 (hunit : unit_supply_proc_model PState)
    (t : instant) : supply_at sched t ≤ 1 := by
  simpa [supply_at] using hunit (sched t)

/-- Unit supply makes instantaneous service either zero or one. -/
theorem unit_supply_proc_service_case
    (hunit : unit_supply_proc_model PState) (j : Job) (t : instant) :
    service_at sched j t = 0 ∨ service_at sched j t = 1 := by
  have hle := (service_at_le_supply_at sched j t).trans
    (supply_at_le_1 sched hunit t)
  cases hs : service_at sched j t with
  | zero => exact Or.inl rfl
  | succ n =>
      rw [hs] at hle
      have hge : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
      have hn : n = 0 := Nat.succ.inj (Nat.le_antisymm hle hge)
      subst n
      exact Or.inr rfl

/-- Supply over an interval of length `δ` is bounded by `δ`. -/
theorem supply_during_bound (hunit : unit_supply_proc_model PState)
    (t δ : instant) :
    supply_during sched t (t + δ) ≤ δ := by
  unfold supply_during
  calc
    (∑ i ∈ Finset.Ico t (t + δ), supply_at sched i) ≤
        ∑ _i ∈ Finset.Ico t (t + δ), (1 : Nat) := by
          apply Finset.sum_le_sum
          intro i _
          exact supply_at_le_1 sched hunit i
    _ = δ := by simp [Nat.card_Ico]

end UnitSupply

/-- A blackout indicator contributes at most one per interval instant. -/
theorem blackout_during_bound (t δ : instant) :
    blackout_during sched t (t + δ) ≤ δ := by
  unfold blackout_during
  calc
    (∑ i ∈ Finset.Ico t (t + δ), (is_blackout sched i).toNat) ≤
        ∑ _i ∈ Finset.Ico t (t + δ), (1 : Nat) := by
          apply Finset.sum_le_sum
          intro i _
          cases is_blackout sched i <;> decide
    _ = δ := by simp [Nat.card_Ico]

/-- Extending an interval by one adds supply at its last instant. -/
theorem supply_during_last_plus_before (t1 t2 : instant) (hle : t1 ≤ t2) :
    supply_during sched t1 (t2 + 1) =
      supply_during sched t1 t2 + supply_at sched t2 := by
  simp only [supply_during]
  rw [Finset.sum_Ico_succ_top hle]

/-- Extending an interval by one adds the last blackout indicator. -/
theorem blackout_during_last_plus_before (t1 t2 : instant) (hle : t1 ≤ t2) :
    blackout_during sched t1 (t2 + 1) =
      blackout_during sched t1 t2 + (is_blackout sched t2).toNat := by
  simp only [blackout_during]
  rw [Finset.sum_Ico_succ_top hle]

/-- `LEAN_HELPER`: pointwise conservation of supply and blackout. -/
private theorem supply_blackout_pointwise (hunit : unit_supply_proc_model PState)
    (t : instant) :
    supply_at sched t + (is_blackout sched t).toNat = 1 := by
  have h := supply_at_complement sched hunit t
  cases hb : is_blackout sched t with
  | false =>
      have ha : supply_at sched t = 1 := by simpa [hb] using h
      simp [ha]
  | true =>
      have ha : supply_at sched t = 0 := by simpa [hb] using h
      simp [ha]

/-- `LEAN_HELPER`: sum conservation over a half-open interval. -/
private theorem supply_blackout_interval_total
    (hunit : unit_supply_proc_model PState) (t δ : instant) :
    supply_during sched t (t + δ) + blackout_during sched t (t + δ) = δ := by
  unfold supply_during blackout_during
  rw [← Finset.sum_add_distrib]
  simp_rw [supply_blackout_pointwise sched hunit]
  simp [Nat.card_Ico]

section UnitSupplyComplements

variable (hunit : unit_supply_proc_model PState)

/-- Interval supply is duration minus blackout count. -/
theorem supply_during_complement (hunit : unit_supply_proc_model PState)
    (t δ : instant) :
    supply_during sched t (t + δ) =
      δ - blackout_during sched t (t + δ) := by
  have h := supply_blackout_interval_total sched hunit t δ
  calc
    supply_during sched t (t + δ) =
        (supply_during sched t (t + δ) +
          blackout_during sched t (t + δ)) -
          blackout_during sched t (t + δ) := by
            exact (Nat.add_sub_cancel_right _ _).symm
    _ = δ - blackout_during sched t (t + δ) := by rw [h]

/-- Interval blackout count is duration minus supply. -/
theorem blackout_during_complement (hunit : unit_supply_proc_model PState)
    (t δ : instant) :
    blackout_during sched t (t + δ) =
      δ - supply_during sched t (t + δ) := by
  have h := supply_blackout_interval_total sched hunit t δ
  calc
    blackout_during sched t (t + δ) =
        (supply_during sched t (t + δ) +
          blackout_during sched t (t + δ)) -
          supply_during sched t (t + δ) := by
            exact (Nat.add_sub_cancel_left _ _).symm
    _ = δ - supply_during sched t (t + δ) := by rw [h]

end UnitSupplyComplements

/-- Blackout counts concatenate across adjacent intervals. -/
theorem blackout_during_cat (t1 t2 t : instant)
    (hle : t1 ≤ t ∧ t ≤ t2) :
    blackout_during sched t1 t + blackout_during sched t t2 =
      blackout_during sched t1 t2 := by
  simp only [blackout_during]
  exact Finset.sum_Ico_consecutive _ hle.1 hle.2

/-- Blackout count grows by at most one per successor step. -/
theorem blackout_during_unit_growth (t : instant) :
    unit_growth_function (blackout_during sched t) := by
  unfold unit_growth_function
  intro t2
  by_cases hle : t ≤ t2
  · rw [show t2 + 1 = t2 + 1 by rfl,
        blackout_during_last_plus_before sched t t2 hle]
    cases is_blackout sched t2 <;> simp
  · have hsucc : t2 + 1 ≤ t := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hle)
    simp [blackout_during, Finset.Ico_eq_empty_of_le, hsucc]

section ConsumedSupply

variable (hconsumed : fully_consuming_proc_model PState)

/-- A scheduled job receives positive service whenever supply is present. -/
theorem progress_inside_supplies
    (hconsumed : fully_consuming_proc_model PState) (j : Job) (t : instant)
    (hsupply : has_supply sched t = true)
    (hscheduled : scheduled_at sched j t = true) :
    0 < service_at sched j t := by
  have hpositive : 0 < supply_at sched t := by
    simpa [has_supply] using hsupply
  have heq := hconsumed j sched t hscheduled
  rw [heq]
  exact hpositive

end ConsumedSupply

end Prosa.Analysis.Facts.Behavior.Supply
