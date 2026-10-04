-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/preemption/fully_preemptive.v

import Prosa.Model.Task.Preemption.Parameters

namespace Prosa.Model.Task.Preemption.FullyPreemptive

open Prosa.Model.Task.Concept
open Prosa.Model.Task.Preemption.Parameters

/-! Representation notes: `ε` is `1`; the source section-local
`#[local] Instance fully_preemptive_rtc_threshold` is a plain
`@[reducible] def` that later translations enable locally. -/

/-- In the fully preemptive model every nonpreemptive segment has length at
most `ε`. -/
@[reducible] def fully_preemptive_task_model {Task : TaskType} [DecidableEq Task] :
    TaskMaxNonpreemptiveSegment Task :=
  ⟨fun _ => 1⟩

/-- The source's section-local run-to-completion threshold: the task cost. -/
@[reducible] def fully_preemptive_rtc_threshold {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] : TaskRunToCompletionThreshold Task :=
  ⟨fun tsk => task_cost tsk⟩

end Prosa.Model.Task.Preemption.FullyPreemptive
