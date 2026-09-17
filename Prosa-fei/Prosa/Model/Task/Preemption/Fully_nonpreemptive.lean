-- Translated from: ../rt-proofs/model/task/preemption/fully_nonpreemptive.v
import Prosa.Model.Task.Preemption.Parameters

namespace Prosa.Model.Task.Preemption.Fully_nonpreemptive

open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Concept
open Prosa.Util.Epsilon

section FullyNonPreemptiveModel

variable {Task : TaskType}
variable [TaskCost Task]

instance fully_nonpreemptive_model : TaskMaxNonpreemptiveSegment Task :=
  ⟨fun tsk => task_cost tsk⟩

end FullyNonPreemptiveModel

section TaskRTCThresholdFullyNonPreemptive

variable {Task : TaskType}

instance fully_nonpreemptive : TaskRunToCompletionThreshold Task :=
  ⟨fun _ => ε⟩

end TaskRTCThresholdFullyNonPreemptive

end Prosa.Model.Task.Preemption.Fully_nonpreemptive
