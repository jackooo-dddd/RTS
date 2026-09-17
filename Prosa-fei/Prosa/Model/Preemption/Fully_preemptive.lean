-- Translated from: ../rt-proofs/model/preemption/fully_preemptive.v
import Prosa.Model.Preemption.Parameter

namespace Prosa.Model.Preemption.Fully_preemptive

open Prosa.Model.Preemption.Parameter
open Prosa.Behavior.Job

section FullyPreemptiveModel

variable {Job : JobType}

/-- In the fully preemptive model, any job can be preempted at any time. -/
instance fully_preemptive_model : JobPreemptable Job where
  job_preemptable (_ : Job) (_ : work) := true

end FullyPreemptiveModel

end Prosa.Model.Preemption.Fully_preemptive
