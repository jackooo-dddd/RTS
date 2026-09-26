-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/always_higher_priority.v

import Prosa.Model.Priority.Classes

namespace Prosa.Analysis.Definitions.AlwaysHigherPriority

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion

/-- `j1` always has higher priority than `j2`: at every time `t`, `j1` is
higher-or-equal priority than `j2` and not conversely. -/
def always_higher_priority {Job : JobType} [DecidableEq Job] [JLDP_policy Job]
    (j1 j2 : Job) : Prop :=
  ∀ t : instant, (hep_job_at t j1 j2 && !hep_job_at t j2 j1) = true

/-- Under a JLFP policy (seen as a JLDP policy through the coercion), the
property is a statement about `hep_job`. -/
theorem always_higher_priority_jlfp {Job : JobType} [DecidableEq Job] [JLFP_policy Job] :
    ∀ j j' : Job,
      always_higher_priority j j' ↔ (hep_job j j' && !hep_job j' j) = true :=
  fun _ _ => ⟨fun h => h 0, fun h _ => h⟩

end Prosa.Analysis.Definitions.AlwaysHigherPriority
