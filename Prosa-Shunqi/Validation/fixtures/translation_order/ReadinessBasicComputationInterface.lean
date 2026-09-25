import Prosa.Model.Readiness.Basic
import Validation.fixtures.translation_order.ServiceComputationInterface

namespace Prosa.Validation.ReadinessBasicInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Validation.ServiceInterface

universe u v w

/-- A kernel-guarded projection of the named local source instance.  The
    service projection is already guarded against the production definition. -/
noncomputable def basicReadyInstanceProjection {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobArrival Job] [JobCost Job] :
    JobReady Job PState where
  job_ready := fun sched j t => pendingProjection sched j t
  ready_implies_pending := by
    intro sched j t ready
    exact ready

theorem basicReadyInstanceProjection_guard :
    @Prosa.Model.Readiness.Basic.basic_ready_instance =
      @basicReadyInstanceProjection := by
  rfl

end Prosa.Validation.ReadinessBasicInterface
