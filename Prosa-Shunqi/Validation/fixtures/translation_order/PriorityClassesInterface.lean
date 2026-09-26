import Prosa.Model.Priority.Classes

/-!
Aggregator-only interface probe for `model/priority/classes.v`: it uses one
declaration from each re-exported module through the aggregator import only.
-/

namespace Prosa.Validation.PriorityClassesInterface

open Prosa.Behavior.Job
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion

theorem classes_exposes_definitions_and_coercion {Job : JobType} [DecidableEq Job]
    (p : JLFP_policy Job) (t : Nat) (j j' : Job) :
    (JLFP_to_JLDP (JLFP := p)).hep_job_at t j j' = p.hep_job j j' := rfl

#print axioms classes_exposes_definitions_and_coercion

end Prosa.Validation.PriorityClassesInterface
