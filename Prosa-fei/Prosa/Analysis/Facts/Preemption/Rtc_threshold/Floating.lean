-- Translated from: ../rt-proofs/analysis/facts/preemption/rtc_threshold/floating.v
import Prosa.Analysis.Facts.Preemption.Task.Floating
import Prosa.Analysis.Facts.Preemption.Rtc_threshold.Job_preemptable
import Prosa.Model.Preemption.Limited_preemptive
import Prosa.Model.Task.Preemption.Floating_nonpreemptive

namespace Prosa.Analysis.Facts.Preemption.Rtc_threshold.Floating

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.Limited_preemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Preemption.Floating_nonpreemptive
open Prosa.Analysis.Facts.Preemption.Rtc_threshold.Job_preemptable

section TaskRTCThresholdFloatingNonPreemptiveRegions

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobCost Job]
variable [JobPreemptable Job]

variable (arr_seq : arrival_sequence Job)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

attribute [local instance] Prosa.Model.Task.Preemption.Floating_nonpreemptive.fully_preemptive

include H_valid_job_cost in
lemma floating_preemptive_valid_task_run_to_completion_threshold :
    ∀ tsk : Task, valid_task_run_to_completion_threshold arr_seq tsk := by
  intro tsk
  refine ⟨?_, ?_⟩
  · -- task_rtc_bounded_by_cost tsk
    show task_cost tsk ≤ task_cost tsk
    exact Nat.le_refl _
  · -- job_respects_task_rtc arr_seq tsk
    intro j ARR TSK
    show job_run_to_completion_threshold j ≤ task_cost tsk
    -- job_run_to_completion_threshold j = job_cost j - (job_last_nonpreemptive_segment j - ε)
    -- so job_run_to_completion_threshold j ≤ job_cost j by Nat.sub_le
    apply Nat.le_trans
    · unfold job_run_to_completion_threshold
      exact Nat.sub_le _ _
    · rw [← TSK]
      exact H_valid_job_cost j ARR

end TaskRTCThresholdFloatingNonPreemptiveRegions

end Prosa.Analysis.Facts.Preemption.Rtc_threshold.Floating
