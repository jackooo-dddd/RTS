import Prosa.Model.Preemption.FullyPreemptive

/-!
Aggregator-only interface probe for `model/preemption/fully_preemptive.v`: it uses
the re-exported preemption-parameter class through the aggregator import only,
together with the translated section-local instance.
-/

namespace Prosa.Validation.FullyPreemptiveInterface

open Prosa.Behavior.Job
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyPreemptive

theorem preemptive_exposes_parameter {Job : JobType} [DecidableEq Job] (j : Job) (ρ : Nat) :
    (fully_preemptive_job_model (Job := Job)).job_preemptable j ρ = true := rfl

#print axioms preemptive_exposes_parameter

end Prosa.Validation.FullyPreemptiveInterface
