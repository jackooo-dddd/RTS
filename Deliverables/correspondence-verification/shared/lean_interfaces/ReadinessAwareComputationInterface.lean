import Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware
import Validation.fixtures.translation_order.BusyPrefixComputationInterface
import Validation.fixtures.translation_order.ReadinessInterferenceComputationInterface

/-!
Export root for `analysis/definitions/service_inversion/readiness_aware.v`: the three definitions, together with
the accepted restricted-supply busy-prefix export root and the accepted readiness-interference root (merged), and the
kernel-guarded list-fold projection of the cumulative service inversion.
-/

open Prosa.Behavior.Job Prosa.Behavior.Ready Prosa.Behavior.Schedule Prosa.Behavior.Time Prosa.Behavior.Arrival_sequence
open Prosa.Model.Priority.Definitions Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware

namespace Prosa.Validation.ReadinessAwareInterface

/-- Source-shaped list-fold projection of the readiness-aware cumulative service inversion. -/
noncomputable def cumulativeServiceInversionProjection {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} [JobReady Job PState] (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 ((List.range' t1 (t2 - t1)).map (fun t => (service_inversion arr_seq sched j t).toNat))

theorem cumulativeServiceInversionProjection_guard :
    @cumulative_service_inversion = @cumulativeServiceInversionProjection := rfl

end Prosa.Validation.ReadinessAwareInterface
