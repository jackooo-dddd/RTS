-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/preemption/fully_nonpreemptive.v

import Prosa.Model.Task.Preemption.Parameters

namespace Prosa.Model.Task.Preemption.FullyNonpreemptive

open Prosa.Model.Task.Concept
open Prosa.Model.Task.Preemption.Parameters

/-! Representation notes: `constant ε` is `fun _ => 1`; the source
section-local `#[local] Instance fully_nonpreemptive_rtc_threshold` is a
plain `@[reducible] def` that later translations enable locally. -/

/-- In the fully nonpreemptive model a task's maximum nonpreemptive segment
is its cost. -/
@[reducible] def fully_nonpreemptive_task_model {Task : TaskType} [DecidableEq Task] [TaskCost Task] :
    TaskMaxNonpreemptiveSegment Task :=
  ⟨fun tsk => task_cost tsk⟩

/-- The source's section-local run-to-completion threshold: once started, a
job runs to completion, so the threshold is `ε`. -/
@[reducible] def fully_nonpreemptive_rtc_threshold {Task : TaskType} [DecidableEq Task] :
    TaskRunToCompletionThreshold Task :=
  ⟨fun _ => 1⟩

end Prosa.Model.Task.Preemption.FullyNonpreemptive
