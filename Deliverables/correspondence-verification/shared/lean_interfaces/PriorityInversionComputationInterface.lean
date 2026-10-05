import Prosa.Analysis.Definitions.PriorityInversion
import Validation.fixtures.translation_order.BusyIntervalClassicalComputationInterface

/-!
Export root for `analysis/definitions/priority_inversion.v`: the production
declarations, the accepted busy-interval export root (preemption-parameter
closure), the accepted `scheduled_jobs_at`, and source-shaped list-fold
projections of the two half-open Boolean sums, tied to the compiled
production definitions by whole-constant kernel guards.
-/

namespace Prosa.Validation.PriorityInversionInterface

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.PriorityInversion

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLFP_policy Job]

/-- Source-shaped half-open Boolean sum of `priority_inversion`. -/
noncomputable def cumulPriorityInversionProjection (j : Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t => (priority_inversion arr_seq sched j t).toNat

theorem cumulPriorityInversionProjection_guard :
    @cumulative_priority_inversion = @cumulPriorityInversionProjection := rfl

/-- Source-shaped half-open Boolean sum of `priority_inversion_cond`. -/
noncomputable def cumulPriorityInversionCondProjection (j : Job) (P : Job → Bool)
    (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t => (priority_inversion_cond arr_seq sched j P t).toNat

theorem cumulPriorityInversionCondProjection_guard :
    @cumulative_priority_inversion_cond = @cumulPriorityInversionCondProjection := rfl

end Prosa.Validation.PriorityInversionInterface
