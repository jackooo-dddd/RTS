-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/task/limited.v

import Prosa.Analysis.Facts.Preemption.Job.Limited
import Prosa.Model.Task.Preemption.LimitedPreemptive

namespace Prosa.Analysis.Facts.Preemption.Task.Limited

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.LimitedPreemptive
open Prosa.Model.Schedule.LimitedPreemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Analysis.Facts.Preemption.Job.Limited
open Prosa.Util.List
open Prosa.Util.Nondecreasing
open Prosa.Model.Task.Preemption.LimitedPreemptive

/-! The fixed-preemption-points model defines a valid preemption model with
bounded nonpreemptive regions.
Binders follow the elaborated source types. The source's section-local
`limited_preemptive_job_model` instance is the accepted Lean definition of
the same name, passed explicitly; the task-level maximum nonpreemptive
segment is the accepted global conversion from task preemption points, as
elaborated. -/

section LimitedPreemptionsModel

variable {Job : JobType} [DecidableEq Job]

/-- LEAN_HELPER: under a valid limited-preemptive job model, every progress
value is followed by a preemption point within the maximum nonpreemptive
segment. -/
private theorem limited_bounded_length [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) (h : valid_limited_preemptions_job_model arr_seq) (j : Job)
    (hj : arrives_in arr_seq j) :
    @nonpreemptive_regions_have_bounded_length Job _ _ limited_preemptive_job_model j := by
  intro ρ hρ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hρ
  have hm := job_parameters_max_np_to_job_limited arr_seq h j hj
  by_cases hin : ρ ∈ job_preemptive_points j
  · refine ⟨ρ, ?_, decide_eq_true hin⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega'
  · obtain ⟨n, hn, hb⟩ := work_belongs_to_some_nonpreemptive_segment arr_seq h j hj ρ hρ.2
      (by simp [hin])
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have hd : (job_preemptive_points j).getD (n + 1) 0 - (job_preemptive_points j).getD n 0 ≤
        max0 (distances (job_preemptive_points j)) :=
      distance_between_neighboring_elements_le_max_distance_in_seq _ n
    refine ⟨(job_preemptive_points j).getD (n + 1) 0, ?_, ?_⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      unfold job_max_nonpreemptive_segment lengths_of_segments
      rw [hm]
      omega'
    · apply decide_eq_true
      rw [List.getD_eq_getElem _ _ hn]
      exact List.getElem_mem _

/-- The fixed-preemption-points model has bounded nonpreemptive regions. -/
theorem fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
    {Task : TaskType} [DecidableEq Task] [TaskCost Task] [JobTask Job Task] [JobCost Job]
    [JobPreemptionPoints Job] [TaskPreemptionPoints Task] (arr_seq : arrival_sequence Job)
    (ts : TaskSet Task) :
    valid_fixed_preemption_points_model arr_seq ts →
      @model_with_bounded_nonpreemptive_segments Task _ Job _ _ _ _ limited_preemptive_job_model arr_seq := by
  intro hv j hj
  refine ⟨?_, limited_bounded_length arr_seq hv.1 j hj⟩
  unfold job_respects_max_nonpreemptive_segment
  apply decide_eq_true
  unfold job_max_nonpreemptive_segment lengths_of_segments
  rw [job_parameters_max_np_to_job_limited arr_seq hv.1 j hj]
  show _ ≤ task_max_nonpr_segment (job_task (Task := Task) j)
  unfold task_max_nonpr_segment
  exact max_of_dominating_seq _ _ (fun n => hv.2.2.2.2.2.1 j n hj)

/-- Hence it is a valid preemption model with bounded nonpreemptive regions. -/
theorem fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
    {Task : TaskType} [DecidableEq Task] [TaskCost Task] [JobTask Job Task] [JobCost Job]
    [JobPreemptionPoints Job] [TaskPreemptionPoints Task] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState) :
    @schedule_respects_preemption_model Job _ PState limited_preemptive_job_model arr_seq sched →
    ∀ ts : TaskSet Task, valid_fixed_preemption_points_model arr_seq ts →
      @valid_model_with_bounded_nonpreemptive_segments Task _ Job _ _ _ _ limited_preemptive_job_model
        PState arr_seq sched := by
  intro hresp ts hv
  exact ⟨valid_fixed_preemption_points_model_lemma arr_seq sched hresp hv.1,
    fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions arr_seq ts hv⟩

end LimitedPreemptionsModel

end Prosa.Analysis.Facts.Preemption.Task.Limited
