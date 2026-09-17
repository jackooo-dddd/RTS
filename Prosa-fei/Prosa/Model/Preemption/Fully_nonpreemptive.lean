-- Translated from: ../rt-proofs/model/preemption/fully_nonpreemptive.v
import Prosa.Model.Preemption.Parameter

namespace Prosa.Model.Preemption.Fully_nonpreemptive

open Prosa.Behavior.Job
open Prosa.Model.Preemption.Parameter

section FullyNonPreemptiveModel

variable {Job : JobType}
variable [JobCost Job]

instance fully_nonpreemptive_model : JobPreemptable Job where
  job_preemptable (j : Job) (ρ : work) := (ρ == 0) || (ρ == job_cost j)

end FullyNonPreemptiveModel

end Prosa.Model.Preemption.Fully_nonpreemptive
