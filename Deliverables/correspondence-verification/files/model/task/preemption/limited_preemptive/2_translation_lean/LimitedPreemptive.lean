-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/preemption/limited_preemptive.v

import Prosa.Model.Task.Preemption.Parameters
import Prosa.Model.Preemption.LimitedPreemptive

namespace Prosa.Model.Task.Preemption.LimitedPreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.LimitedPreemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-! Representation notes: `tsk \in ts` in `Prop` position is
`decide (tsk ∈ ts) = true`; `size s` is `s.length`; `nth 0 s n` is
`s.getD n 0`; `ε` is `1`; `first0`, `last0`, `distances` and
`nondecreasing_sequence` are the accepted utilities; the source section-local
`#[local] Instance limited_preemptions_rtc_threshold` is a plain
`@[reducible] def`. Binder orders follow the elaborated types (unused section
context is absent). -/

section ValidModelWithFixedPreemptionPoints

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskPreemptionPoints Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable [JobPreemptionPoints Job]
variable (arr_seq : arrival_sequence Job) (ts : TaskSet Task)

/-- Every task's first preemption point is `0`. -/
def task_beginning_of_execution_in_preemption_points : Prop :=
  ∀ tsk, decide (tsk ∈ ts) = true → first0 (task_preemption_points tsk) = 0

/-- Every task's last preemption point is its cost. -/
def task_end_of_execution_in_preemption_points : Prop :=
  ∀ tsk, decide (tsk ∈ ts) = true → last0 (task_preemption_points tsk) = task_cost tsk

/-- Every task's preemption points form a nondecreasing sequence. -/
def nondecreasing_task_preemption_points : Prop :=
  ∀ tsk, decide (tsk ∈ ts) = true → nondecreasing_sequence (task_preemption_points tsk)

/-- Every arriving job has as many preemption points as its task. -/
def consistent_job_segment_count : Prop :=
  ∀ j, arrives_in arr_seq j →
    (job_preemptive_points j).length = (task_preemption_points (job_task (Task := Task) j)).length

/-- Every job segment is no longer than the corresponding task segment. -/
def job_respects_segment_lengths : Prop :=
  ∀ j (n : Nat), arrives_in arr_seq j →
    (distances (job_preemptive_points j)).getD n 0 ≤
      (distances (task_preemption_points (job_task (Task := Task) j))).getD n 0

/-- Every task segment is nonempty. -/
def task_segments_are_nonempty : Prop :=
  ∀ tsk (n : Nat), decide (tsk ∈ ts) = true →
    n < (distances (task_preemption_points tsk)).length →
      1 ≤ (distances (task_preemption_points tsk)).getD n 0

/-- The task-level conditions of the fixed-preemption-points model. -/
def valid_fixed_preemption_points_task_model : Prop :=
  task_beginning_of_execution_in_preemption_points ts ∧
  task_end_of_execution_in_preemption_points ts ∧
  nondecreasing_task_preemption_points ts ∧
  consistent_job_segment_count (Task := Task) arr_seq ∧
  job_respects_segment_lengths (Task := Task) arr_seq ∧
  task_segments_are_nonempty ts

/-- The fixed-preemption-points model: valid job- and task-level conditions. -/
def valid_fixed_preemption_points_model : Prop :=
  valid_limited_preemptions_job_model arr_seq ∧
  valid_fixed_preemption_points_task_model arr_seq ts

end ValidModelWithFixedPreemptionPoints

/-- The source's section-local run-to-completion threshold of the
limited-preemptive task model. -/
@[reducible] def limited_preemptions_rtc_threshold {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskPreemptionPoints Task] : TaskRunToCompletionThreshold Task :=
  ⟨fun tsk => task_cost tsk - (task_last_nonpr_segment tsk - 1)⟩

end Prosa.Model.Task.Preemption.LimitedPreemptive
