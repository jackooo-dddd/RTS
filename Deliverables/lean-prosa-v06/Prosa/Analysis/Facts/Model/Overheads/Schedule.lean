-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/overheads/schedule.v

import Prosa.Model.Processor.Overheads
import Prosa.Analysis.Facts.BusyInterval.Pi

namespace Prosa.Analysis.Facts.Model.Overheads.Schedule

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.Overheads
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.WorkConserving
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.BusyInterval.HepAtPt

/-! Basic properties of the processor model with explicit overheads.
Binders follow the elaborated source types (the unused arrival and cost
contexts are absent where the source statement does not use them).
Representation: a Boolean in `Prop` position is `= true`; `P <-> Q` is `↔`.
The source's `Global Hint Resolve` registration is proof automation only. -/

section OverheadsProcProperties

variable {Job : JobType} [DecidableEq Job]

private theorem sched_iff (j : Job) (s : (processor_state Job).State) :
    ProcessorState.scheduled_in (processor_state Job) j s = true ↔
      overheads_scheduled_on j (show proc_state Job from s) () = true := by
  rw [ProcessorState.scheduled_in_eq_true_iff]
  constructor
  · rintro ⟨c, hc⟩; cases c; exact hc
  · intro h; exact ⟨(), h⟩

private theorem supply_in_eq (s : (processor_state Job).State) :
    ProcessorState.supply_in (processor_state Job) s = overheads_supply_on (show proc_state Job from s) () := by
  rfl

private theorem service_in_eq (j : Job) (s : (processor_state Job).State) :
    ProcessorState.service_in (processor_state Job) j s = overheads_service_on j (show proc_state Job from s) () := by
  rfl

private theorem uni_state (s : proc_state Job) (j1 j2 : Job) :
    overheads_scheduled_on j1 s () = true → overheads_scheduled_on j2 s () = true → j1 = j2 := by
  cases s with
  | Idle => simp [overheads_scheduled_on]
  | ContextSwitch a b =>
    cases b with
    | none => simp [overheads_scheduled_on]
    | some b => simp [overheads_scheduled_on]; intro h1 h2; rw [h1, h2]
  | Dispatch a =>
    cases a with
    | none => simp [overheads_scheduled_on]
    | some a => simp [overheads_scheduled_on]; intro h1 h2; rw [h1, h2]
  | CacheRelatedPreemptionDelay a => simp [overheads_scheduled_on]; intro h1 h2; rw [h1, h2]
  | Progress a => simp [overheads_scheduled_on]; intro h1 h2; rw [h1, h2]

private theorem consuming_state (s : proc_state Job) (j : Job) :
    overheads_scheduled_on j s () = true → overheads_service_on j s () = overheads_supply_on s () := by
  cases s with
  | Idle => simp [overheads_scheduled_on]
  | ContextSwitch a b =>
    cases b with
    | none => simp [overheads_scheduled_on]
    | some b => simp [overheads_scheduled_on, overheads_service_on, overheads_supply_on]
  | Dispatch a =>
    cases a with
    | none => simp [overheads_scheduled_on]
    | some a => simp [overheads_scheduled_on, overheads_service_on, overheads_supply_on]
  | CacheRelatedPreemptionDelay a => simp [overheads_scheduled_on, overheads_service_on, overheads_supply_on]
  | Progress a =>
    simp only [overheads_scheduled_on, overheads_service_on, overheads_supply_on, decide_eq_true_eq]
    intro h; subst h; simp

/-- The processor model with overheads is a uniprocessor model. -/
theorem overheads_proc_model_is_a_uniprocessor_model :
    uniprocessor_model (processor_state Job) := by
  intro j1 j2 sched t h1 h2
  exact uni_state (sched t) j1 j2 ((sched_iff j1 (sched t)).1 h1) ((sched_iff j2 (sched t)).1 h2)

/-- The processor model with overheads supplies at most one unit. -/
theorem overheads_proc_model_provides_unit_supply :
    unit_supply_proc_model (processor_state Job) := by
  intro s
  rw [supply_in_eq s]
  cases (show proc_state Job from s) <;> simp [overheads_supply_on]

/-- The processor model with overheads is fully consuming. -/
theorem overheads_proc_model_fully_consuming :
    fully_consuming_proc_model (processor_state Job) := by
  intro j sched t h
  unfold service_at supply_at
  rw [service_in_eq j (sched t), supply_in_eq (sched t)]
  exact consuming_state (sched t) j ((sched_iff j (sched t)).1 h)

end OverheadsProcProperties

section OverheadScheduleProperties

variable {Job : JobType} [DecidableEq Job]

private theorem sched_job_state (s : proc_state Job) (j : Job) :
    overheads_scheduled_on j s () = true ↔
      proc_state.casesOn (motive := fun _ => Option Job) s none (fun _ oj => oj) (fun oj => oj)
        (fun j => some j) (fun j => some j) = some j := by
  cases s with
  | Idle => simp [overheads_scheduled_on]
  | ContextSwitch a b =>
    cases b with
    | none => simp [overheads_scheduled_on]
    | some b => simp [overheads_scheduled_on, eq_comm]
  | Dispatch a =>
    cases a with
    | none => simp [overheads_scheduled_on]
    | some a => simp [overheads_scheduled_on, eq_comm]
  | CacheRelatedPreemptionDelay a => simp [overheads_scheduled_on, eq_comm]
  | Progress a => simp [overheads_scheduled_on, eq_comm]

/-- Either no job or some job is associated with the processor state. -/
theorem scheduled_job_dec (sched : schedule (processor_state Job)) :
    ∀ t : instant, scheduled_job sched t = none ∨ ∃ j : Job, scheduled_job sched t = some j := by
  intro t
  cases h : scheduled_job sched t with
  | none => exact Or.inl rfl
  | some j => exact Or.inr ⟨j, rfl⟩

/-- `scheduled_at` and `scheduled_job` agree. -/
theorem scheduled_at_iff_scheduled_job (sched : schedule (processor_state Job)) :
    ∀ (j : Job) (t : instant), scheduled_at sched j t = true ↔ scheduled_job sched t = some j := by
  intro j t
  exact (sched_iff j (sched t)).trans (sched_job_state (sched t) j)

end OverheadScheduleProperties

section ScheduledInBusyPrefix

variable {Job : JobType} [DecidableEq Job]

/-- Inside a busy-interval prefix some job is scheduled at every instant. -/
theorem job_scheduled_in_busy_interval_prefix [JobArrival Job] [JobCost Job] (JLFP : JLFP_policy Job) :
    reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule (processor_state Job)) [JobReady Job (processor_state Job)],
      work_bearing_readiness arr_seq sched → valid_schedule sched arr_seq →
      work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
      ∃ jo : Job, scheduled_at sched jo t = true := by
  intro hrefl arr_seq hva sched _ hwb hvs hwc j ha hpos t1 t2 hbip t ht
  rcases scheduled_at_cases arr_seq hva sched hvs.1
      (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) t with hidle | h
  · exact absurd hidle (instant_t_is_not_idle arr_seq hva sched JLFP hrefl hwb hvs hwc j ha hpos t1 t2
      hbip t ht)
  · exact h

end ScheduledInBusyPrefix

end Prosa.Analysis.Facts.Model.Overheads.Schedule
