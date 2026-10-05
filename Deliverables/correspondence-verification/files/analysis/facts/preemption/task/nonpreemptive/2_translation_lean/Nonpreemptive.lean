-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/task/nonpreemptive.v

import Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
import Prosa.Model.Task.Preemption.FullyNonpreemptive

namespace Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyNonpreemptive
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FullyNonpreemptive
open Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive

/-! Representation notes: the source enables the section-local
`fully_nonpreemptive_job_model` and `fully_nonpreemptive_task_model`
instances with `#[local] Existing Instance`; the statements pass the accepted
Lean definitions of the same names explicitly, as the elaborated source types
do. Binder orders follow the elaborated types (unused section context and
hypotheses are absent, as in the elaborated source). -/

/-- The fully nonpreemptive model has bounded nonpreemptive regions. -/
theorem fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions
    {Task : TaskType} [DecidableEq Task] [TaskCost Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      @model_with_bounded_nonpreemptive_segments Task _ Job _ _ _
        fully_nonpreemptive_task_model fully_nonpreemptive_job_model arr_seq := by
  intro hvalid j harr
  have hmax := job_max_nps_is_job_cost (Job := Job) j
  refine ⟨?_, ?_⟩
  · unfold job_respects_max_nonpreemptive_segment
    rw [hmax]
    have hv := hvalid j harr
    simp only [valid_job_cost, decide_eq_true_eq] at hv
    exact decide_eq_true hv
  · intro ρ hρ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hρ
    by_cases h0 : ρ = 0
    · refine ⟨ρ, ?_, ?_⟩
      · simp
      · show (decide (ρ = 0) || decide (ρ = job_cost j)) = true
        simp [h0]
    · refine ⟨job_cost j, ?_, ?_⟩
      · rw [hmax]; simp only [Bool.and_eq_true, decide_eq_true_eq]
        try dsimp only [work, duration, instant] at *
        omega
      · show (decide (job_cost j = 0) || decide (job_cost j = job_cost j)) = true
        simp

/-- The fully nonpreemptive model is a valid preemption model with bounded
nonpreemptive regions. -/
theorem fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions
    {Task : TaskType} [DecidableEq Task] [TaskCost Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} :
    unit_service_proc_model PState →
      ∀ sched : schedule PState, nonpreemptive_schedule sched → completed_jobs_dont_execute sched →
        arrivals_have_valid_job_costs (Task := Task) arr_seq →
          @valid_model_with_bounded_nonpreemptive_segments Task _ Job _ _ _
            fully_nonpreemptive_task_model fully_nonpreemptive_job_model PState arr_seq sched := by
  intro hunit sched hnp hcjde hvalid
  exact ⟨valid_fully_nonpreemptive_model arr_seq hunit sched hnp hcjde,
    fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions arr_seq hvalid⟩

end Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
