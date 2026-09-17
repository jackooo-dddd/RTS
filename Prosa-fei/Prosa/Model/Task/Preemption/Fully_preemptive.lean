-- Translated from: ../rt-proofs/model/task/preemption/fully_preemptive.v
import Prosa.Model.Task.Preemption.Parameters

namespace Prosa.Model.Task.Preemption.Fully_preemptive

open Prosa.Model.Task.Preemption.Parameters
open Prosa.Util.Epsilon
open Prosa.Model.Task.Concept

section FullyPreemptiveModel

variable {Task : TaskType}

instance fully_preemptive_model : TaskMaxNonpreemptiveSegment Task where
  task_max_nonpreemptive_segment := fun _ => ε

end FullyPreemptiveModel

section TaskRTCThresholdFullyPreemptiveModel

variable {Task : TaskType}
variable [TaskCost Task]

instance fully_preemptive : TaskRunToCompletionThreshold Task where
  task_run_to_completion_threshold := fun tsk => task_cost tsk

end TaskRTCThresholdFullyPreemptiveModel

end Prosa.Model.Task.Preemption.Fully_preemptive
