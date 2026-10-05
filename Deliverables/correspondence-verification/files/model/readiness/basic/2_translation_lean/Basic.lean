-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/readiness/basic.v

import Prosa.Behavior.All

namespace Prosa.Model.Readiness.Basic

open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

universe u v w

/-- `LEAN_HELPER` for the source's local instance. Its explicit name remains
available to downstream modules, while it is not registered globally as a
`JobReady` instance. In the basic model, precisely the pending jobs are ready. -/
noncomputable def basic_ready_instance {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobArrival Job] [JobCost Job] :
    JobReady Job PState where
  job_ready := fun sched j t => pending sched j t
  ready_implies_pending := by
    intro sched j t ready
    exact ready

end Prosa.Model.Readiness.Basic
