-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/task/floating.v

import Prosa.Model.Preemption.LimitedPreemptive
import Prosa.Model.Task.Preemption.FloatingNonpreemptive
import Prosa.Analysis.Facts.Preemption.Job.Limited

namespace Prosa.Analysis.Facts.Preemption.Task.Floating

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
open Prosa.Model.Task.Preemption.FloatingNonpreemptive

/-! The model with floating nonpreemptive regions defines a valid preemption
model with bounded nonpreemptive regions.
Binders follow the elaborated source types. The source's section-local
`limited_preemptive_job_model` instance is the accepted Lean definition of
the same name, passed explicitly. -/

section FloatingNonPreemptiveRegionsModel

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

/-- The floating model has bounded nonpreemptive regions. -/
theorem floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobCost Job]
    [TaskMaxNonpreemptiveSegment Task] [JobPreemptionPoints Job] (arr_seq : arrival_sequence Job) :
    valid_model_with_floating_nonpreemptive_regions (Task := Task) arr_seq →
      @model_with_bounded_nonpreemptive_segments Task _ Job _ _ _ _ limited_preemptive_job_model arr_seq := by
  intro hv j hj
  exact ⟨decide_eq_true (hv.2 j hj), limited_bounded_length arr_seq hv.1 j hj⟩

/-- Hence it is a valid preemption model with bounded nonpreemptive regions. -/
theorem floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobCost Job]
    [TaskMaxNonpreemptiveSegment Task] [JobPreemptionPoints Job] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState) :
    @schedule_respects_preemption_model Job _ PState limited_preemptive_job_model arr_seq sched →
    valid_model_with_floating_nonpreemptive_regions (Task := Task) arr_seq →
      @valid_model_with_bounded_nonpreemptive_segments Task _ Job _ _ _ _ limited_preemptive_job_model
        PState arr_seq sched := by
  intro hresp hv
  exact ⟨valid_fixed_preemption_points_model_lemma arr_seq sched hresp hv.1,
    floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions arr_seq hv⟩

end FloatingNonPreemptiveRegionsModel

end Prosa.Analysis.Facts.Preemption.Task.Floating
