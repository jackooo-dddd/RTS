import Prosa.Analysis.Definitions.ReadinessInterference
import Validation.fixtures.translation_order.ArrivalSequenceComputationInterface
import Validation.fixtures.translation_order.AbstractDefinitionsComputationInterface

namespace Prosa.Validation.ReadinessInterferenceInterface

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.ReadinessInterference

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job} [JobReady Job PState]
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLFP_policy Job]

/-- Source-shaped half-open Boolean sum, tied to the compiled production
definition by the whole-constant kernel guard below. -/
noncomputable def cumulReadinessInterferenceProjection
    (j : Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      (!some_hep_job_ready arr_seq sched j t).toNat

theorem cumulReadinessInterferenceProjection_guard :
    @cumulative_readiness_interference = @cumulReadinessInterferenceProjection := rfl

end Prosa.Validation.ReadinessInterferenceInterface
