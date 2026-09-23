-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/sbf/periodic.v

import Prosa.Model.Processor.Supply

namespace Prosa.Analysis.Definitions.Sbf.Periodic

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply

section PeriodicResourceModel

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}

/-- Every interval `[period * k, period * (k + 1))` receives at least
    `allocation` units of supply. The period must be positive. -/
noncomputable def periodic_resource_model
    (period allocation : duration) (sched : schedule PState) : Prop :=
  period > 0 ∧ period ≥ allocation ∧
    ∀ k : Nat,
      supply_during sched (period * k) (period * (k + 1)) ≥ allocation

end PeriodicResourceModel

section PeriodicResourceModelSBF

/-- The periodic resource-model supply bound. Nat subtraction is truncated,
    as in the authoritative MathComp source. -/
def prm_sbf (period allocation delta : duration) : duration :=
  let blackout := period - allocation
  let n_full_periods := (delta - blackout) / period
  let supply_in_full_periods := n_full_periods * allocation
  let duration_of_full_periods := n_full_periods * period
  supply_in_full_periods + (delta - 2 * blackout - duration_of_full_periods)

end PeriodicResourceModelSBF

end Prosa.Analysis.Definitions.Sbf.Periodic
