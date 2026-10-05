-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/ideal/cumulative_bounds.v

import Prosa.Analysis.Abstract.Ideal.IwInstantiation

namespace Prosa.Analysis.Abstract.Ideal.CumulativeBounds

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.Ideal
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Abstract.Ideal.IwInstantiation

/-! Inequalities that hold inside the busy interval of a job, for the JLFP instantiation of interference and
interfering workload on ideal uniprocessors.

Binders follow the elaborated source types: the section inputs and hypotheses used by each lemma, in their
elaborated order (the unused sequential-tasks hypothesis is absent). The section-local instances
`ideal_jlfp_interference` / `ideal_jlfp_interfering_workload` re-expose the accepted instantiation of
`iw_instantiation` at the section's arrival sequence and schedule; they are passed explicitly to the abstract busy
interval, as in the elaborated types. A Boolean in `Prop` position is `= true`. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- A bounded priority inversion bounds the cumulative priority inversion inside the busy interval. -/
theorem cumulative_priority_inversion_is_bounded [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [JR : JobReady Job (processor_state Job)] [JLFP : JLFP_policy Job] :
    reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), valid_schedule sched arr_seq →
    ∀ (tsk : Task) (j : Job), arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : duration,
      @Prosa.Analysis.Abstract.Definitions.busy_interval Job _ (ideal_jlfp_interference arr_seq sched)
        (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t1 t2 →
    ∀ Δ : duration, t1 + Δ ≤ t2 →
    ∀ priority_inversion_bound : duration → duration,
      priority_inversion_is_bounded_by arr_seq sched tsk priority_inversion_bound →
        cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) ≤ priority_inversion_bound (job_arrival j - t1) := by
  intro hrefl arr_seq hva sched hvs tsk j harr htsk hpos t1 t2 hbi Δ hΔ B hB
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hvs.1 hmust hcde hrefl j harr
    hpos t1 t2).mpr hbi
  have hle : cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) ≤
      cumulative_priority_inversion arr_seq sched j t1 t2 := by
    unfold cumulative_priority_inversion
    exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hΔ)
  have hc : 0 < job_cost j := by
    unfold job_cost_positive at hpos; exact of_decide_eq_true hpos
  exact Nat.le_trans hle (hB j harr htsk hc t1 t2 hcl.1)

/-- The cumulative interference from higher-or-equal-priority jobs of other tasks is bounded by their total
service. -/
theorem cumulative_interference_is_bounded_by_total_service [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [JR : JobReady Job (processor_state Job)] [JLFP : JLFP_policy Job] :
    reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), valid_schedule sched arr_seq →
    ∀ (tsk : Task) (j : Job), arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : duration,
      @Prosa.Analysis.Abstract.Definitions.busy_interval Job _ (ideal_jlfp_interference arr_seq sched)
        (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t1 t2 →
    ∀ Δ : duration,
      cumulative_another_task_hep_job_interference (Task := Task) arr_seq sched j t1 (t1 + Δ) ≤
        service_of_jobs sched (fun jo => another_task_hep_job (Task := Task) jo j)
          (arrivals_between arr_seq t1 (t1 + Δ)) t1 (t1 + Δ) := by
  intro hrefl arr_seq hva sched hvs tsk j harr htsk hpos t1 t2 hbi Δ
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hvs.1 hmust hcde hrefl j harr
    hpos t1 t2).mpr hbi
  rw [cumulative_i_thep_eq_service_of_othep (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq hva sched hmust
    hcde JLFP (ideal_proc_model_provides_unit_service Job) j t1 (t1 + Δ) hcl.1.2.1]
  exact Nat.le_refl _

end Prosa.Analysis.Abstract.Ideal.CumulativeBounds
