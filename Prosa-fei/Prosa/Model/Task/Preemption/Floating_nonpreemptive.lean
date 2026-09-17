-- Translated from: ../rt-proofs/model/task/preemption/floating_nonpreemptive.v
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Model.Preemption.Limited_preemptive

namespace Prosa.Model.Task.Preemption.Floating_nonpreemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.Limited_preemptive
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Preemption.Parameters

section ValidModelWithFloatingNonpreemptiveRegions

variable {Task : TaskType}
variable [TaskMaxNonpreemptiveSegment Task]
variable {Job : JobType}
variable [JobArrival Job]
variable [JobTask Job Task]
variable [JobCost Job]
variable [JobPreemptionPoints Job]

variable (arr_seq : arrival_sequence Job)

def job_respects_task_max_np_segment :=
  ∀ (j : Job),
    arrives_in arr_seq j →
    job_max_nonpreemptive_segment j ≤ task_max_nonpreemptive_segment (job_task (Task := Task) j)

def valid_model_with_floating_nonpreemptive_regions :=
  valid_limited_preemptions_job_model arr_seq ∧
  job_respects_task_max_np_segment (Task := Task) arr_seq

end ValidModelWithFloatingNonpreemptiveRegions

section TaskRTCThresholdFloatingNonPreemptiveRegions

variable {Task : TaskType}
variable [TaskCost Task]

instance fully_preemptive : TaskRunToCompletionThreshold Task where
  task_run_to_completion_threshold (tsk : Task) := task_cost tsk

end TaskRTCThresholdFloatingNonPreemptiveRegions

end Prosa.Model.Task.Preemption.Floating_nonpreemptive
