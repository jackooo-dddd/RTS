-- Translated from: ../rt-proofs/analysis/facts/preemption/rtc_threshold/preemptive.v
import Prosa.Model.Preemption.Fully_preemptive
import Prosa.Model.Task.Preemption.Fully_preemptive
import Prosa.Analysis.Facts.Preemption.Rtc_threshold.Job_preemptable

namespace Prosa.Analysis.Facts.Preemption.Rtc_threshold.Preemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Concept

section TaskRTCThresholdFullyPreemptiveModel

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

attribute [local instance] Prosa.Model.Task.Preemption.Fully_preemptive.fully_preemptive

include H_valid_job_cost in
lemma fully_preemptive_valid_task_run_to_completion_threshold :
    ∀ tsk : Task, valid_task_run_to_completion_threshold arr_seq tsk := by
  intro tsk
  constructor
  · unfold task_rtc_bounded_by_cost
    simp [Prosa.Model.Task.Preemption.Fully_preemptive.fully_preemptive, task_run_to_completion_threshold]
  · intro j ARR TSK
    simp [Prosa.Model.Task.Preemption.Fully_preemptive.fully_preemptive, task_run_to_completion_threshold]
    apply Nat.le_trans
    · exact Nat.sub_le _ _
    · rw [← TSK]
      exact H_valid_job_cost j ARR

end TaskRTCThresholdFullyPreemptiveModel

end Prosa.Analysis.Facts.Preemption.Rtc_threshold.Preemptive
