-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/ideal/schedule.v

import Prosa.Model.Processor.Ideal
import Prosa.Model.Processor.PlatformProperties
import Prosa.Model.Schedule.Scheduled
import Prosa.Analysis.Facts.Model.Scheduled

namespace Prosa.Analysis.Facts.Model.Ideal.Schedule

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled

/-! The classes to which an ideal schedule belongs. Every lemma takes the
job type (with its decidable equality) explicitly and fixes the processor
model to `processor_state Job`, as in the elaborated source types; the unused
section classes `JobArrival`/`JobCost` are absent there and here. -/

/-- Deciding `s = some j` on an ideal state is deciding it on `Option Job`
(the source's `s == Some j`). The ideal state carrier is not
instance-reducible, so this instance is stated for that exact comparison. -/
local instance idealStateDecidableEqSome {Job : JobType} [DecidableEq Job]
    (s : (processor_state Job).State) (j : Job) : Decidable (s = some j) :=
  (inferInstance : DecidableEq (Option Job)) s (some j)

private theorem ideal_scheduled_in_eq {Job : JobType} [DecidableEq Job]
    (j : Job) (s : (processor_state Job).State) :
    ProcessorState.scheduled_in (processor_state Job) j s = decide (s = some j) := by
  change (Finset.univ : Finset Unit).fold Bool.or false (fun _ => decide (s = some j)) =
    decide (s = some j)
  rw [Finset.univ_unique, Finset.fold_singleton]
  cases decide (s = some j) <;> rfl

private theorem ideal_service_in_eq {Job : JobType} [DecidableEq Job]
    (j : Job) (s : (processor_state Job).State) :
    ProcessorState.service_in (processor_state Job) j s = (decide (s = some j)).toNat := by
  change (∑ _c : Unit, (if decide (s = some j) then 1 else 0)) = (decide (s = some j)).toNat
  rw [Fintype.sum_unique]
  cases decide (s = some j) <;> rfl

private theorem ideal_supply_in_eq {Job : JobType} [DecidableEq Job] (s : (processor_state Job).State) :
    ProcessorState.supply_in (processor_state Job) s = 1 := by
  change (∑ _c : Unit, 1) = 1
  rw [Fintype.sum_unique]

/-- The ideal processor model is a uni-processor model. -/
theorem ideal_proc_model_is_a_uniprocessor_model (Job : JobType) [DecidableEq Job] :
    uniprocessor_model (processor_state Job) := by
  intro j1 j2 sched t h1 h2
  unfold scheduled_at at h1 h2
  rw [ideal_scheduled_in_eq j1 (sched t)] at h1
  rw [ideal_scheduled_in_eq j2 (sched t)] at h2
  have e1 := of_decide_eq_true h1
  have e2 := of_decide_eq_true h2
  rw [e1] at e2
  exact Option.some.inj e2

/-- `service_in` is the service on the unique core. -/
theorem service_in_service_on (Job : JobType) [DecidableEq Job] (j : Job)
    (s : (processor_state Job).State) :
    ProcessorState.service_in (processor_state Job) j s =
      (processor_state Job).service_on j s () := by
  rw [ideal_service_in_eq]
  change _ = (if decide (s = some j) then 1 else 0)
  cases decide (s = some j) <;> rfl

/-- `service_in` is the Boolean state comparison. -/
theorem service_in_def (Job : JobType) [DecidableEq Job] (j : Job)
    (s : (processor_state Job).State) :
    ProcessorState.service_in (processor_state Job) j s = (decide (s = some j)).toNat :=
  ideal_service_in_eq j s

/-- The ideal processor model is an ideal-progress model. -/
theorem ideal_proc_model_ensures_ideal_progress (Job : JobType) [DecidableEq Job] :
    ideal_progress_proc_model (processor_state Job) := by
  intro j s h
  rw [ideal_scheduled_in_eq j s] at h
  rw [ideal_service_in_eq j s, h]
  decide

/-- The ideal processor model is a unit-service model. -/
theorem ideal_proc_model_provides_unit_service (Job : JobType) [DecidableEq Job] :
    unit_service_proc_model (processor_state Job) := by
  intro j s
  rw [ideal_service_in_eq j s]
  cases decide (s = some j) <;> decide

/-- The ideal processor model is a unit-supply model. -/
theorem ideal_proc_model_provides_unit_supply (Job : JobType) [DecidableEq Job] :
    unit_supply_proc_model (processor_state Job) := by
  intro s
  exact Nat.le_of_eq (ideal_supply_in_eq s)

/-- `scheduled_in` is the Boolean state comparison. -/
theorem scheduled_in_def (Job : JobType) [DecidableEq Job] (j : Job)
    (s : (processor_state Job).State) :
    ProcessorState.scheduled_in (processor_state Job) j s = decide (s = some j) :=
  ideal_scheduled_in_eq j s

/-- `scheduled_at` is the Boolean schedule comparison. -/
theorem scheduled_at_def (Job : JobType) [DecidableEq Job]
    (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    scheduled_at sched j t = decide (sched t = some j) :=
  ideal_scheduled_in_eq j (sched t)

/-- `service_on` is the Boolean state comparison. -/
theorem service_on_def (Job : JobType) [DecidableEq Job] (j : Job)
    (s : (processor_state Job).State) (c : (processor_state Job).Core) :
    (processor_state Job).service_on j s c = (decide (s = some j)).toNat := by
  change (if decide (s = some j) then 1 else 0) = (decide (s = some j)).toNat
  cases decide (s = some j) <;> rfl

/-- `service_at` is the Boolean schedule comparison. -/
theorem service_at_def (Job : JobType) [DecidableEq Job]
    (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    service_at sched j t = (decide (sched t = some j)).toNat :=
  ideal_service_in_eq j (sched t)

/-- `service_in` coincides with `scheduled_in`. -/
theorem service_in_is_scheduled_in (Job : JobType) [DecidableEq Job] (j : Job)
    (s : (processor_state Job).State) :
    ProcessorState.service_in (processor_state Job) j s =
      (ProcessorState.scheduled_in (processor_state Job) j s).toNat := by
  rw [ideal_service_in_eq, ideal_scheduled_in_eq]

/-- `service_at` coincides with `scheduled_at`. -/
theorem service_at_is_scheduled_at (Job : JobType) [DecidableEq Job]
    (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    service_at sched j t = (scheduled_at sched j t).toNat :=
  service_in_is_scheduled_in Job j (sched t)

/-- The ideal processor model is fully supply-consuming. -/
theorem ideal_proc_model_fully_consuming (Job : JobType) [DecidableEq Job] :
    fully_consuming_proc_model (processor_state Job) := by
  intro j sched t h
  rw [scheduled_at_def] at h
  unfold service_at supply_at
  rw [ideal_service_in_eq j (sched t), h, ideal_supply_in_eq (sched t)]
  rfl

/-- The ideal uniprocessor always has supply. -/
theorem ideal_proc_has_supply (Job : JobType) [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t : instant) :
    has_supply sched t = true := by
  unfold has_supply supply_at
  rw [ideal_supply_in_eq (sched t)]
  decide

/-- Case analysis on the state of an ideal schedule. -/
theorem ideal_proc_model_sched_case_analysis (Job : JobType) [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t : instant) :
    ideal_is_idle sched t = true ∨ ∃ j : Job, scheduled_at sched j t = true := by
  cases h : sched t with
  | none => left; unfold ideal_is_idle; rw [h]
  | some j => right; exact ⟨j, by rw [scheduled_at_def]; exact decide_eq_true h⟩

/-- A scheduled job means the processor is not idle. -/
theorem ideal_sched_implies_not_idle (Job : JobType) [DecidableEq Job]
    (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    scheduled_at sched j t = true → ¬ ideal_is_idle sched t = true := by
  intro h hidle
  rw [scheduled_at_def] at h
  have e := of_decide_eq_true h
  unfold ideal_is_idle at hidle
  rw [e] at hidle
  exact Bool.false_ne_true hidle

/-- An idle processor provides no service. -/
theorem ideal_not_idle_implies_sched (Job : JobType) [DecidableEq Job]
    (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    ideal_is_idle sched t = true → service_at sched j t = 0 := by
  intro hidle
  rw [service_at_def]
  cases h : sched t with
  | none => rfl
  | some k => unfold ideal_is_idle at hidle; rw [h] at hidle; exact absurd hidle Bool.false_ne_true

/-- The generic `scheduled_job_at` coincides with the ideal processor state. -/
theorem scheduled_job_at_def (Job : JobType) [DecidableEq Job]
    (arr_seq : arrival_sequence Job) [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_come_from_arrival_sequence sched arr_seq →
    jobs_must_arrive_to_execute sched →
    valid_arrival_sequence arr_seq →
    ∀ t : instant, scheduled_job_at arr_seq sched t = sched t := by
  intro hfrom hmust hva t
  open Prosa.Analysis.Facts.Model.Scheduled in
  cases h : sched t with
  | some j =>
      have hs : scheduled_at sched j t = true := by rw [scheduled_at_def]; exact decide_eq_true h
      have := scheduled_job_at_scheduled_at arr_seq hva sched hfrom hmust
        (ideal_proc_model_is_a_uniprocessor_model Job) j t
      rw [hs] at this
      exact of_decide_eq_true this
  | none =>
      apply (scheduled_job_at_none arr_seq hva sched hfrom hmust t).2
      intro j
      rw [scheduled_at_def, h]
      simp

/-- The generic and ideal notions of idle instants coincide. -/
theorem is_idle_def (Job : JobType) [DecidableEq Job]
    (arr_seq : arrival_sequence Job) [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_come_from_arrival_sequence sched arr_seq →
    jobs_must_arrive_to_execute sched →
    valid_arrival_sequence arr_seq →
    ∀ t : instant, is_idle arr_seq sched t = ideal_is_idle sched t := by
  intro hfrom hmust hva t
  rw [Prosa.Analysis.Facts.Model.Scheduled.is_idle_iff,
    scheduled_job_at_def Job arr_seq sched hfrom hmust hva t]
  unfold ideal_is_idle
  cases sched t <;> simp

end Prosa.Analysis.Facts.Model.Ideal.Schedule
