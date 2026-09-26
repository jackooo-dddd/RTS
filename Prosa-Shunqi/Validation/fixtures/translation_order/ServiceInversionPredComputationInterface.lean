import Prosa.Analysis.Definitions.ServiceInversion.Pred
import Validation.fixtures.translation_order.PreemptionParameterComputationInterface

/-!
Export root for `analysis/definitions/service_inversion/pred.v`: the
production declarations, the accepted preemption-parameter export root, a
kernel-guarded list-fold projection of the half-open service-inversion sum
(replaced during export only after its unparameterized `rfl` guard is
checked, as for the accepted service sums), and kernel-checked constructor
equations for `List.any`.
-/

namespace Prosa.Validation.ServiceInversionPredInterface

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.ServiceInversion.Pred

universe u

noncomputable def cumulativeServiceInversionProjection {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLDP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      (service_inversion arr_seq sched j t).toNat

theorem cumulativeServiceInversionProjection_guard :
    @cumulative_service_inversion = @cumulativeServiceInversionProjection := rfl

theorem production_any_nil {X : Type u} (p : X → Bool) : ([] : List X).any p = false := rfl

theorem production_any_cons {X : Type u} (p : X → Bool) (x : X) (xs : List X) :
    (x :: xs).any p = (p x || xs.any p) := rfl

end Prosa.Validation.ServiceInversionPredInterface
