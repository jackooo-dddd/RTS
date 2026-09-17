-- Translated from: ../rt-proofs/model/task/preemption/parameters.v
import Prosa.Model.Preemption.Parameter
import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Preemption.Parameters

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Concept
open Prosa.Util.List
open Prosa.Util.Epsilon

class TaskMaxNonpreemptiveSegment (Task : TaskType) where
  task_max_nonpreemptive_segment : Task → work

export TaskMaxNonpreemptiveSegment (task_max_nonpreemptive_segment)

class TaskRunToCompletionThreshold (Task : TaskType) where
  task_run_to_completion_threshold : Task → work

export TaskRunToCompletionThreshold (task_run_to_completion_threshold)

class TaskPreemptionPoints (Task : TaskType) where
  task_preemption_points : Task → List work

export TaskPreemptionPoints (task_preemption_points)

section MaxAndLastNonpreemptiveSegment

variable {Task : TaskType}
variable [TaskPreemptionPoints Task]

def task_max_nonpr_segment (tsk : Task) :=
  max0 (distances (task_preemption_points tsk))

def task_last_nonpr_segment (tsk : Task) :=
  last0 (distances (task_preemption_points tsk))

end MaxAndLastNonpreemptiveSegment

instance TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
    (Task : TaskType) [TaskPreemptionPoints Task] : TaskMaxNonpreemptiveSegment Task :=
  ⟨task_max_nonpr_segment⟩

section ValidPreemptionModel

variable {Task : TaskType}
variable {Job : JobType}
variable [JobArrival Job]
variable [JobTask Job Task]
variable [JobCost Job]
variable [TaskMaxNonpreemptiveSegment Task]
variable [JobPreemptable Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

def job_respects_max_nonpreemptive_segment (j : Job) :=
  job_max_nonpreemptive_segment j ≤ task_max_nonpreemptive_segment (job_task (Task := Task) j)

def nonpreemptive_regions_have_bounded_length (j : Job) :=
  ∀ (ρ : duration),
    0 ≤ ρ ∧ ρ ≤ job_cost j →
    ∃ (pp : duration),
      ρ ≤ pp ∧ pp ≤ ρ + (job_max_nonpreemptive_segment j - ε) ∧
      job_preemptable j pp = true

def model_with_bounded_nonpreemptive_segments :=
  ∀ j,
    arrives_in arr_seq j →
    job_respects_max_nonpreemptive_segment (Task := Task) j
    ∧ nonpreemptive_regions_have_bounded_length j

def valid_model_with_bounded_nonpreemptive_segments :=
  valid_preemption_model arr_seq sched ∧
  model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq

end ValidPreemptionModel

section ValidTaskRunToCompletionThreshold

variable {Task : TaskType}
variable [TaskCost Task]
variable {Job : JobType}
variable [JobArrival Job]
variable [JobTask Job Task]
variable [JobCost Job]
variable [JobPreemptable Job]
variable [TaskRunToCompletionThreshold Task]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

def task_rtc_bounded_by_cost (tsk : Task) :=
  task_run_to_completion_threshold tsk ≤ task_cost tsk

def job_respects_task_rtc (tsk : Task) :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_run_to_completion_threshold j ≤ task_run_to_completion_threshold tsk

def valid_task_run_to_completion_threshold (tsk : Task) :=
  task_rtc_bounded_by_cost tsk ∧
  job_respects_task_rtc arr_seq tsk

end ValidTaskRunToCompletionThreshold

end Prosa.Model.Task.Preemption.Parameters
