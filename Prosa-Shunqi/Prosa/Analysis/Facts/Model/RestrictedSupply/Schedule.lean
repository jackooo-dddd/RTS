-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/restricted_supply/schedule.v

import Prosa.Model.Processor.PlatformProperties
import Prosa.Model.Processor.RestrictedSupply

namespace Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Processor.RestrictedSupply
open Prosa.Model.Processor.Supply

variable {Job : JobType} [DecidableEq Job]

private theorem rs_scheduled_at_iff (sched : schedule (rs_processor_state Job))
    (j : Job) (t : instant) :
    scheduled_at sched j t = true ↔ rs_scheduled_on j (sched t) = true := by
  rw [scheduled_at, ProcessorState.scheduled_in_eq_true_iff]
  constructor
  · rintro ⟨r, hr⟩
    cases r
    exact hr
  · intro h
    exact ⟨(), h⟩

private theorem rs_supply_in_eq (s : processor_state Job) :
    ProcessorState.supply_in (rs_processor_state Job) s = rs_supply_on s := by
  change (∑ _ : Unit, rs_supply_on s) = rs_supply_on s
  simp

private theorem rs_service_in_eq (j : Job) (s : processor_state Job) :
    ProcessorState.service_in (rs_processor_state Job) j s = rs_service_on j s := by
  change (∑ _ : Unit, rs_service_on j s) = rs_service_on j s
  simp

/-- A restricted-supply schedule has at most one scheduled job at each instant. -/
theorem rs_proc_model_is_a_uniprocessor_model :
    uniprocessor_model (rs_processor_state Job) := by
  intro j1 j2 sched t h1 h2
  have h1' := (rs_scheduled_at_iff sched j1 t).mp h1
  have h2' := (rs_scheduled_at_iff sched j2 t).mp h2
  cases hst : sched t with
  | Idle => simp [rs_scheduled_on, hst] at h1'
  | Active j =>
      simp [rs_scheduled_on, hst] at h1' h2'
      exact h1'.symm.trans h2'
  | Unavailable j =>
      simp [rs_scheduled_on, hst] at h1' h2'
      exact h1'.symm.trans h2'
  | Inactive => simp [rs_scheduled_on, hst] at h1'

/-- Every restricted-supply processor state supplies at most one unit. -/
theorem rs_proc_is_unit_supply :
    unit_supply_proc_model (rs_processor_state Job) := by
  intro s
  change (∑ _ : Unit, rs_supply_on (s : processor_state Job)) ≤ 1
  cases s <;> simp [rs_supply_on]

/-- Every scheduled job receives all supply available in its state. -/
theorem rs_proc_model_fully_consuming :
    fully_consuming_proc_model (rs_processor_state Job) := by
  intro j sched t hscheduled
  have h := (rs_scheduled_at_iff sched j t).mp hscheduled
  change (∑ _ : Unit, rs_service_on j (sched t)) =
    (∑ _ : Unit, rs_supply_on (sched t))
  cases hst : sched t with
  | Idle => simp [rs_scheduled_on, hst] at h
  | Active j' =>
      simp [rs_scheduled_on, hst] at h
      simp [rs_service_on, rs_supply_on, h]
  | Unavailable j' => simp [rs_service_on, rs_supply_on]
  | Inactive => simp [rs_scheduled_on, hst] at h

end Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule
