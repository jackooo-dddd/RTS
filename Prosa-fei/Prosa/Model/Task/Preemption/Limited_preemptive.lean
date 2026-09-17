-- Translated from: ../rt-proofs/model/task/preemption/limited_preemptive.v
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Model.Preemption.Limited_preemptive

namespace Prosa.Model.Task.Preemption.Limited_preemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter hiding job_preemption_points distances
open Prosa.Model.Preemption.Limited_preemptive
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Util.List
open Prosa.Util.Nondecreasing
open Prosa.Util.Epsilon

section ValidModelWithFixedPreemptionPoints

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskPreemptionPoints Task]

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [JobPreemptionPoints Job]

variable (arr_seq : arrival_sequence Job)
variable (ts : TaskSet Task)

def task_beginning_of_execution_in_preemption_points :=
  ∀ tsk, tsk ∈ ts → first0 (task_preemption_points tsk) = 0

def task_end_of_execution_in_preemption_points :=
  ∀ tsk, tsk ∈ ts → last0 (task_preemption_points tsk) = task_cost tsk

def nondecreasing_task_preemption_points :=
  ∀ tsk, tsk ∈ ts → nondecreasing_sequence (task_preemption_points tsk)

def consistent_job_segment_count :=
  ∀ j,
    arrives_in arr_seq j →
    (job_preemption_points j).length = (task_preemption_points (job_task (Task := Task) j)).length

def job_respects_segment_lengths :=
  ∀ j n,
    arrives_in arr_seq j →
    (distances (job_preemption_points j)).getD n 0
    ≤ (distances (task_preemption_points (job_task (Task := Task) j))).getD n 0

def task_segments_are_nonempty :=
  ∀ tsk n,
    tsk ∈ ts →
    n < (distances (task_preemption_points tsk)).length →
    ε ≤ (distances (task_preemption_points tsk)).getD n 0

def valid_fixed_preemption_points_task_model :=
  task_beginning_of_execution_in_preemption_points ts ∧
  task_end_of_execution_in_preemption_points ts ∧
  nondecreasing_task_preemption_points ts ∧
  consistent_job_segment_count (Task := Task) arr_seq ∧
  job_respects_segment_lengths (Task := Task) arr_seq ∧
  task_segments_are_nonempty ts

def valid_fixed_preemption_points_model :=
  valid_limited_preemptions_job_model arr_seq ∧
  valid_fixed_preemption_points_task_model (Task := Task) arr_seq ts

end ValidModelWithFixedPreemptionPoints

section TaskRTCThresholdLimitedPreemptions

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskPreemptionPoints Task]

instance limited_preemptions : TaskRunToCompletionThreshold Task where
  task_run_to_completion_threshold (tsk : Task) :=
    task_cost tsk - (task_last_nonpr_segment tsk - ε)

end TaskRTCThresholdLimitedPreemptions

end Prosa.Model.Task.Preemption.Limited_preemptive
