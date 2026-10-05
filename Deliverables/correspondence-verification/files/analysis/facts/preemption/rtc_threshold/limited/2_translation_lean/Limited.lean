-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/rtc_threshold/limited.v

import Prosa.Analysis.Facts.Preemption.Task.Limited
import Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
import Prosa.Model.Task.Preemption.LimitedPreemptive

namespace Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.LimitedPreemptive
open Prosa.Model.Schedule.LimitedPreemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.LimitedPreemptive
open Prosa.Analysis.Facts.Preemption.Job.Limited
open Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-! The run-to-completion threshold of the fixed-preemption-points model is
valid. Binders follow the elaborated source types. The source's section-local
`limited_preemptive_job_model` and `limited_preemptions_rtc_threshold`
instances are the accepted Lean definitions of the same names, passed
explicitly. Representation: `tsk \in ts` is `decide (tsk ∈ ts) = true`,
`size` is `List.length`, `ε` is `1`. -/

section TaskRTCThresholdLimitedPreemptions

variable {Job : JobType} [DecidableEq Job]

/-- A task with positive cost has at least two preemption points. -/
theorem number_of_preemption_points_in_task_at_least_two {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskPreemptionPoints Task] [JobTask Job Task] [JobCost Job]
    [JobPreemptionPoints Job] (arr_seq : arrival_sequence Job) (ts : TaskSet Task) :
    valid_fixed_preemption_points_model arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true → 0 < task_cost tsk →
      1 < (task_preemption_points tsk).length := by
  intro hv tsk hin hpos
  have hbeg := hv.2.1 tsk hin
  have hend := hv.2.2.1 tsk hin
  revert hbeg hend
  cases task_preemption_points tsk with
  | nil => intro _ hend; simp [last0] at hend; omega'
  | cons a t =>
    cases t with
    | nil => intro hbeg hend; simp [first0, last0] at hbeg hend; omega'
    | cons b t' => intro _ _; simp

/-- The limited-preemptive run-to-completion threshold is valid. -/
theorem limited_valid_task_run_to_completion_threshold {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskPreemptionPoints Task] [JobTask Job Task] [JobCost Job]
    [JobPreemptionPoints Job] (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) :
    @schedule_respects_preemption_model Job _ PState limited_preemptive_job_model arr_seq sched →
    ∀ ts : TaskSet Task, valid_fixed_preemption_points_model arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true → 0 < task_cost tsk →
      @valid_task_run_to_completion_threshold Task _ _ Job _ _ _ limited_preemptive_job_model
        limited_preemptions_rtc_threshold arr_seq tsk := by
  intro hresp ts hv tsk hin hpos
  refine ⟨decide_eq_true (Nat.sub_le _ _), ?_⟩
  intro j hj htsk
  have hjt : job_task (Task := Task) j = tsk := by unfold job_of_task at htsk; exact of_decide_eq_true htsk
  have hvpm := valid_fixed_preemption_points_model_lemma arr_seq sched hresp hv.1
  show @job_rtct Job _ _ limited_preemptive_job_model j ≤
    task_cost tsk - (task_last_nonpr_segment tsk - 1)
  unfold job_rtct
  rcases Nat.eq_zero_or_pos (job_cost j) with hz | hcpos
  · rw [hz]; omega'
  have hJpos := @job_last_nonpreemptive_segment_positive Job _ _ limited_preemptive_job_model PState arr_seq
    sched hvpm j hj (by unfold job_cost_positive; exact decide_eq_true hcpos)
  have hJle := @job_last_nonpreemptive_segment_le_job_cost Job _ _ limited_preemptive_job_model PState arr_seq
    sched hvpm j hj
  have h2t := number_of_preemption_points_in_task_at_least_two arr_seq ts hv tsk hin hpos
  have hsortT := hv.2.2.2.1 tsk hin
  have hendT := hv.2.2.1 tsk hin
  have hTle : task_last_nonpr_segment tsk ≤ task_cost tsk := by
    unfold task_last_nonpr_segment
    rw [← hendT]
    exact Nat.le_trans (last_of_seq_le_max_of_seq _) (max_distance_in_seq_le_last_element_of_seq _ hsortT)
  have hTpos : 0 < task_last_nonpr_segment tsk := by
    unfold task_last_nonpr_segment
    rw [last0_nth]
    have hlen := size_of_seq_of_distances _ (by omega' : 2 ≤ (task_preemption_points tsk).length)
    exact hv.2.2.2.2.2.2 tsk _ hin (by omega')
  -- the job-level last segment through the deduplicated preemption points
  have hsortJ := hv.1.2.2 j hj
  have hendJ := hv.1.2.1 j hj
  have hJ : @job_last_nonpreemptive_segment Job _ _ limited_preemptive_job_model j =
      last0 (distances (job_preemptive_points j).dedup) := by
    unfold job_last_nonpreemptive_segment lengths_of_segments
    rw [job_parameters_last_np_to_job_limited arr_seq hv.1 j hj]
    congr 1
    have := distances_positive_undup _ hsortJ
    simpa [gt_iff_lt] using this
  have hcostJ : job_cost j = last0 (job_preemptive_points j).dedup := by
    rw [last0_undup _ hsortJ, hendJ]
  have hlastJ := last_seq_minus_last_distance_seq _ (nondecreasing_sequence_undup _ hsortJ)
  have hund := undup_nth_le _ hsortJ
  have hlastT := last_seq_minus_last_distance_seq _ hsortT
  have h2j := number_of_preemption_points_at_least_two arr_seq hv.1 j hj
    (by unfold job_cost_positive; exact decide_eq_true hcpos)
  have hlenJT := hv.2.2.2.2.1 j hj
  rw [hjt] at hlenJT
  have hdom := domination_of_distances_implies_domination_of_seq (job_preemptive_points j)
    (task_preemption_points tsk)
    (by rw [zero_is_first_element arr_seq hv.1 j hj]; exact Nat.zero_le _)
    (by omega') (by omega') hlenJT hsortJ hsortT
    (fun n => by have := hv.2.2.2.2.2.1 j n hj; rw [hjt] at this; exact this)
    ((job_preemptive_points j).length - 2)
  have hlenJT' : (job_preemptive_points j).length - 2 = (task_preemption_points tsk).length - 2 := by
    rw [hlenJT]
  rw [hlenJT'] at hdom hund
  unfold task_last_nonpr_segment at hTle hTpos ⊢
  rw [hJ] at hJpos hJle ⊢
  rw [hcostJ] at hJle ⊢
  rw [hendT] at hlastT
  omega'

/-- The last nonpreemptive segment of a task is its cost minus its
run-to-completion threshold, plus `ε`. -/
theorem last_segment_eq_cost_minus_rtct {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskPreemptionPoints Task] [JobTask Job Task] [JobCost Job]
    [JobPreemptionPoints Job] (arr_seq : arrival_sequence Job) (ts : TaskSet Task) :
    valid_fixed_preemption_points_model arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
      task_cost tsk - @task_rtct Task _ limited_preemptions_rtc_threshold tsk =
        task_last_nonpr_segment tsk - 1 := by
  intro hv tsk hin
  have hendT := hv.2.2.1 tsk hin
  have hsortT := hv.2.2.2.1 tsk hin
  have hTle : task_last_nonpr_segment tsk ≤ task_cost tsk := by
    unfold task_last_nonpr_segment
    rw [← hendT]
    exact Nat.le_trans (last_of_seq_le_max_of_seq _) (max_distance_in_seq_le_last_element_of_seq _ hsortT)
  show task_cost tsk - (task_cost tsk - (task_last_nonpr_segment tsk - 1)) = _
  omega'

end TaskRTCThresholdLimitedPreemptions

end Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited
