-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/preemption/floating_nonpreemptive.v

import Prosa.Model.Preemption.LimitedPreemptive
import Prosa.Model.Task.Preemption.Parameters

namespace Prosa.Model.Task.Preemption.FloatingNonpreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.LimitedPreemptive
open Prosa.Model.Task.Preemption.Parameters

/-! Representation notes: the source enables the job-level
`limited_preemptive_job_model` with `#[local] Existing Instance`; the
definitions below pass the accepted Lean definition of the same name
explicitly, as the elaborated source does. The source section-local
`#[local] Instance floating_preemptive_rtc_threshold` is a plain
`@[reducible] def`. Binder orders follow the elaborated types. -/

section ValidModelWithFloatingNonpreemptiveRegions

variable {Task : TaskType} [DecidableEq Task] [TaskMaxNonpreemptiveSegment Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
variable [JobPreemptionPoints Job]
variable (arr_seq : arrival_sequence Job)

/-- Every arriving job's maximum nonpreemptive segment is bounded by its task's. -/
def job_respects_task_max_np_segment : Prop :=
  ∀ j : Job, arrives_in arr_seq j →
    @job_max_nonpreemptive_segment Job _ _ limited_preemptive_job_model j ≤
      task_max_nonpreemptive_segment (job_task (Task := Task) j)

/-- A valid model with floating nonpreemptive regions. -/
def valid_model_with_floating_nonpreemptive_regions : Prop :=
  valid_limited_preemptions_job_model arr_seq ∧
  job_respects_task_max_np_segment (Task := Task) arr_seq

end ValidModelWithFloatingNonpreemptiveRegions

/-- The source's section-local run-to-completion threshold: the task cost. -/
@[reducible] def floating_preemptive_rtc_threshold {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] : TaskRunToCompletionThreshold Task :=
  ⟨fun tsk => task_cost tsk⟩

end Prosa.Model.Task.Preemption.FloatingNonpreemptive
