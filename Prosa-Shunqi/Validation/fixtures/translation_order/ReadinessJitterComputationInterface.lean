import Prosa.Model.Readiness.Jitter
import Validation.fixtures.translation_order.ServiceComputationInterface

namespace Prosa.Validation.ReadinessJitterInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Readiness.Jitter
open Prosa.Validation.ServiceInterface

/-- A kernel-guarded projection of the named source-local jitter instance.
    Its `completed_by` observation goes through the already guarded Service
    projection, so the export carries the actual computation body. -/
noncomputable def jitterReadyInstanceProjection {Job : JobType} [DecidableEq Job]
    [JobArrival Job] [JobJitter Job] {PState : ProcessorState Job} [JobCost Job] :
    JobReady Job PState where
  job_ready := fun sched j t => is_released j t && !completedByProjection sched j t
  ready_implies_pending := by
    intro sched j t h
    have hparts := Bool.and_eq_true_iff.mp h
    have hrel : job_arrival j + job_jitter j ≤ t := of_decide_eq_true hparts.1
    have harr : job_arrival j ≤ t :=
      Nat.le_trans (Nat.le_add_right (job_arrival j) (job_jitter j)) hrel
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true harr, hparts.2⟩

theorem jitterReadyInstanceProjection_guard :
    @jitter_ready_instance = @jitterReadyInstanceProjection := by
  rfl

end Prosa.Validation.ReadinessJitterInterface
