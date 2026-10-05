-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/readiness/jitter.v

import Prosa.Behavior.All
import Prosa.Util.Nat

namespace Prosa.Model.Readiness.Jitter

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u

/-- A job's release jitter, measured as a duration after its arrival. -/
class JobJitter (Job : JobType) [DecidableEq Job] where
  job_jitter : Job → duration

export JobJitter (job_jitter)

/-- Auxiliary observation of the Boolean operation selected by the
source-local readiness instance. -/
def jitter_ready_bool (released completed : Bool) : Bool :=
  released && !completed

section ReadinessOfJitteryJobs

variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job] [JobJitter Job]

/-- A job has been released once its arrival plus jitter has passed. -/
def is_released (j : Job) (t : instant) : Bool :=
  decide (job_arrival j + job_jitter j ≤ t)

variable {PState : ProcessorState Job} [JobCost Job]

/-- The source-local readiness instance for jittery jobs. Its instance
registration is local to the source section; the constructor remains
available as a named definition without globally selecting this model. -/
noncomputable local instance jitter_ready_instance : JobReady Job PState where
  job_ready sched j t := is_released j t && !completed_by sched j t
  ready_implies_pending sched j t h := by
    have hparts := Bool.and_eq_true_iff.mp h
    have hrel : job_arrival j + job_jitter j ≤ t := by
      exact of_decide_eq_true hparts.1
    have harr : job_arrival j ≤ t :=
      Nat.le_trans (Nat.le_add_right (job_arrival j) (job_jitter j)) hrel
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true harr, hparts.2⟩

/-- Kernel-checkable interface guard for the source-local instance field. -/
theorem jitter_ready_instance_field_guard
    (sched : schedule PState) (j : Job) (t : instant) :
    (jitter_ready_instance (PState := PState)).job_ready sched j t =
      jitter_ready_bool (is_released j t) (completed_by sched j t) := by
  rfl

theorem jitter_ready_instance_pending_guard
    (sched : schedule PState) (j : Job) (t : instant)
    (h : (jitter_ready_instance (PState := PState)).job_ready sched j t = true) :
    pending sched j t = true :=
  (jitter_ready_instance (PState := PState)).ready_implies_pending sched j t h

end ReadinessOfJitteryJobs

end Prosa.Model.Readiness.Jitter
