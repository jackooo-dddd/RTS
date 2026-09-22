import Prosa.Model.Processor.Supply
import Validation.fixtures.translation_order.ScheduleComputationInterface

namespace Prosa.Validation.SupplyInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply

universe u

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}

/-!
Source-shaped projections for the five production definitions. The exporter
may replace a production body with one of these smaller interfaces only after
the corresponding whole-constant `rfl` guard is accepted by the Lean kernel.
-/

noncomputable def supplyAtProjection
    (sched : schedule PState) (t : instant) : work :=
  ProcessorState.supply_in PState (sched t)

noncomputable def supplyDuringProjection
    (sched : schedule PState) (t1 t2 : instant) : work :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      supplyAtProjection sched t

noncomputable def hasSupplyProjection
    (sched : schedule PState) (t : instant) : Bool :=
  decide (0 < supplyAtProjection sched t)

noncomputable def isBlackoutProjection
    (sched : schedule PState) (t : instant) : Bool :=
  !hasSupplyProjection sched t

noncomputable def blackoutDuringProjection
    (sched : schedule PState) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      (isBlackoutProjection sched t).toNat

theorem supplyAtProjection_guard :
    @supply_at = @supplyAtProjection := rfl

theorem supplyDuringProjection_guard :
    @supply_during = @supplyDuringProjection := rfl

theorem hasSupplyProjection_guard :
    @has_supply = @hasSupplyProjection := rfl

theorem isBlackoutProjection_guard :
    @is_blackout = @isBlackoutProjection := rfl

theorem blackoutDuringProjection_guard :
    @blackout_during = @blackoutDuringProjection := rfl

end Prosa.Validation.SupplyInterface
