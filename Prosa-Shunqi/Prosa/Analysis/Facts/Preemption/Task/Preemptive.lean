-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/task/preemptive.v

import Prosa.Analysis.Facts.Preemption.Job.Preemptive
import Prosa.Model.Task.Preemption.FullyPreemptive

namespace Prosa.Analysis.Facts.Preemption.Task.Preemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FullyPreemptive
open Prosa.Analysis.Facts.Preemption.Job.Preemptive

/-! Representation notes: the source enables the section-local
`fully_preemptive_job_model` and `fully_preemptive_task_model` instances with
`#[local] Existing Instance`; the statements pass the accepted Lean
definitions of the same names explicitly, as the elaborated source types do.
Binder orders follow the elaborated types (unused section context, including
`TaskCost`, `JobArrival` and the run-to-completion threshold, is absent). -/

/-- The fully preemptive model has bounded nonpreemptive regions. -/
theorem fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions
    {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] (arr_seq : arrival_sequence Job) :
    @model_with_bounded_nonpreemptive_segments Task _ Job _ _ _
      fully_preemptive_task_model fully_preemptive_job_model arr_seq := by
  intro j _
  refine ⟨?_, ?_⟩
  · unfold job_respects_max_nonpreemptive_segment
    by_cases h : job_cost j = 0
    · rw [job_max_nps_is_0 j h]; rfl
    · rw [job_max_nps_is_ε j (Nat.pos_of_ne_zero h)]; rfl
  · intro ρ _
    refine ⟨ρ, ?_, rfl⟩
    simp

/-- The fully preemptive model is a valid preemption model with bounded
nonpreemptive segments. -/
theorem fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments
    {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    @valid_model_with_bounded_nonpreemptive_segments Task _ Job _ _ _
      fully_preemptive_task_model fully_preemptive_job_model PState arr_seq sched :=
  ⟨valid_fully_preemptive_model arr_seq sched,
    fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions arr_seq⟩

end Prosa.Analysis.Facts.Preemption.Task.Preemptive
