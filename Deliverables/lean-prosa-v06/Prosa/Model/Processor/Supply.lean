-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/supply.v

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Prosa.Behavior.Schedule

namespace Prosa.Model.Processor.Supply

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open scoped BigOperators

universe u v w

section Supply

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (sched : schedule PState)

/-- Supply available at instant `t`. -/
noncomputable def supply_at (t : instant) : work :=
  ProcessorState.supply_in PState (sched t)

/-- Cumulative supply in the half-open interval `[t1, t2)`. -/
noncomputable def supply_during (t1 t2 : instant) : work :=
  ∑ t ∈ Finset.Ico t1 t2, supply_at sched t

/-- Boolean observation that the instantaneous supply is positive. -/
noncomputable def has_supply (t : instant) : Bool :=
  decide (0 < supply_at sched t)

/-- Boolean observation that no supply is available at `t`. -/
noncomputable def is_blackout (t : instant) : Bool :=
  !has_supply sched t

/-- Number of blackout instants in the half-open interval `[t1, t2)`. -/
noncomputable def blackout_during (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (is_blackout sched t).toNat

end Supply

end Prosa.Model.Processor.Supply
