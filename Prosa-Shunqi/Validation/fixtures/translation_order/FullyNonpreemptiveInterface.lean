import Prosa.Model.Preemption.FullyNonpreemptive

/-!
Aggregator-only interface probe for `model/preemption/fully_nonpreemptive.v`: it uses
the re-exported preemption-parameter class through the aggregator import only,
together with the translated section-local instance.
-/

namespace Prosa.Validation.FullyNonpreemptiveInterface

open Prosa.Behavior.Job
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyNonpreemptive

theorem nonpreemptive_exposes_parameter {Job : JobType} [DecidableEq Job] [JobCost Job] (j : Job) :
    (fully_nonpreemptive_job_model (Job := Job)).job_preemptable j 0 = true := rfl

#print axioms nonpreemptive_exposes_parameter

end Prosa.Validation.FullyNonpreemptiveInterface
