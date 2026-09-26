-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/preemption/parameters.v

import Prosa.Model.Preemption.Parameter
import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Preemption.Parameters

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-! Representation notes: `a <= b <= c` in `Prop` position is
`(decide (a ≤ b) && decide (b ≤ c)) = true`; `b` Boolean in `Prop` position
is `b = true`; `ε` is `1`; `max0`, `last0` and `distances` are the accepted
utilities; the source `#[global] Instance` conversion is a Lean global
instance. Binder orders follow the elaborated types (unused section context
is absent). -/

/-- Task-level bound on the length of nonpreemptive segments. -/
class TaskMaxNonpreemptiveSegment (Task : TaskType) [DecidableEq Task] where
  task_max_nonpreemptive_segment : Task → work

export TaskMaxNonpreemptiveSegment (task_max_nonpreemptive_segment)

/-- Task-level run-to-completion threshold. -/
class TaskRunToCompletionThreshold (Task : TaskType) [DecidableEq Task] where
  task_rtct : Task → work

export TaskRunToCompletionThreshold (task_rtct)

/-- Task-level preemption points. -/
class TaskPreemptionPoints (Task : TaskType) [DecidableEq Task] where
  task_preemption_points : Task → List work

export TaskPreemptionPoints (task_preemption_points)

section MaxAndLastNonpreemptiveSegment

variable {Task : TaskType} [DecidableEq Task] [TaskPreemptionPoints Task]

/-- The longest nonpreemptive segment of a task. -/
def task_max_nonpr_segment (tsk : Task) : Nat :=
  max0 (distances (task_preemption_points tsk))

/-- The last nonpreemptive segment of a task. -/
def task_last_nonpr_segment (tsk : Task) : Nat :=
  last0 (distances (task_preemption_points tsk))

end MaxAndLastNonpreemptiveSegment

/-- Task preemption points determine the task's maximum nonpreemptive segment. -/
instance TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion (Task : TaskType)
    [DecidableEq Task] [TaskPreemptionPoints Task] : TaskMaxNonpreemptiveSegment Task :=
  ⟨task_max_nonpr_segment⟩

section ValidPreemptionModel

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- A job's maximum nonpreemptive segment is bounded by its task's. -/
def job_respects_max_nonpreemptive_segment [JobTask Job Task] [JobCost Job]
    [TaskMaxNonpreemptiveSegment Task] [JobPreemptable Job] (j : Job) : Bool :=
  decide (job_max_nonpreemptive_segment j ≤
    task_max_nonpreemptive_segment (job_task (Task := Task) j))

/-- Every progress value is followed by a preemption point within the job's
maximum nonpreemptive segment. -/
def nonpreemptive_regions_have_bounded_length [JobCost Job] [JobPreemptable Job]
    (j : Job) : Prop :=
  ∀ ρ : duration, (decide (0 ≤ ρ) && decide (ρ ≤ job_cost j)) = true →
    ∃ pp : duration,
      (decide (ρ ≤ pp) && decide (pp ≤ ρ + (job_max_nonpreemptive_segment j - 1))) = true ∧
      job_preemptable j pp = true

/-- Every arriving job respects both nonpreemptive-segment properties. -/
def model_with_bounded_nonpreemptive_segments [JobTask Job Task] [JobCost Job]
    [TaskMaxNonpreemptiveSegment Task] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j, arrives_in arr_seq j →
    job_respects_max_nonpreemptive_segment (Task := Task) j = true ∧
    nonpreemptive_regions_have_bounded_length j

/-- A valid preemption model with bounded nonpreemptive segments. -/
def valid_model_with_bounded_nonpreemptive_segments [JobTask Job Task] [JobCost Job]
    [TaskMaxNonpreemptiveSegment Task] [JobPreemptable Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) : Prop :=
  valid_preemption_model arr_seq sched ∧
  model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq

end ValidPreemptionModel

section ValidTaskRunToCompletionThreshold

variable {Task : TaskType} [DecidableEq Task]

/-- A task's run-to-completion threshold is at most its cost. -/
def task_rtc_bounded_by_cost [TaskCost Task] [TaskRunToCompletionThreshold Task]
    (tsk : Task) : Bool :=
  decide (task_rtct tsk ≤ task_cost tsk)

/-- Every arriving job of the task has a run-to-completion threshold bounded
by the task's. -/
def job_respects_task_rtc {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    [JobPreemptable Job] [TaskRunToCompletionThreshold Task]
    (arr_seq : arrival_sequence Job) (tsk : Task) : Prop :=
  ∀ j, arrives_in arr_seq j → job_of_task tsk j = true → job_rtct j ≤ task_rtct tsk

/-- A valid task run-to-completion threshold. -/
def valid_task_run_to_completion_threshold [TaskCost Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [JobPreemptable Job] [TaskRunToCompletionThreshold Task]
    (arr_seq : arrival_sequence Job) (tsk : Task) : Prop :=
  task_rtc_bounded_by_cost tsk = true ∧ job_respects_task_rtc arr_seq tsk

end ValidTaskRunToCompletionThreshold

end Prosa.Model.Task.Preemption.Parameters
