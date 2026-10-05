-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/readiness/suspension.v

import Prosa.Behavior.All
import Prosa.Analysis.Definitions.Progress
import Prosa.Util.Nat

namespace Prosa.Model.Readiness.Suspension

open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Analysis.Definitions.Progress

/-! Readiness of self-suspending jobs.

Representation: a Boolean in `Prop` position is `= true`; `a <= b` in a Boolean position is `decide (a ≤ b)`;
`~~ b` is `!b`; `\sum_(0 <= ρ < n) F ρ` is the list fold `List.foldr Nat.add 0 ((List.range' 0 n).map F)`
(the ascending `index_iota` enumeration summed from the right). The source's section-local readiness instance
`suspension_ready_instance` is a named definition of the same name, not a global instance. -/

/-- After having received `rho` units of service, a job `j` may self-suspend for `job_suspension j rho` time
units (zero if it remains ready). -/
class JobSuspension (Job : JobType) [DecidableEq Job] where
  job_suspension : Job → work → duration

export JobSuspension (job_suspension)

section ReadinessOfSelfSuspendingJobs

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable [JobArrival Job] [JobCost Job] [JobSuspension Job]

/-- A job's current self-suspension has passed at `t` if it arrived at least `delay` time units ago and has not
progressed within the last `delay` time units, where `delay` is the suspension incurred at its current service. -/
noncomputable def suspension_has_passed (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  let delay := job_suspension j (service sched j t)
  decide (job_arrival j + delay ≤ t) && no_progress_for sched j t delay

/-- A pending job is self-suspended at `t` if its current suspension has not yet passed. -/
noncomputable def suspended (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  !suspension_has_passed sched j t && pending sched j t

/-- LEAN_HELPER for the source's section-local instance: a self-suspending job is ready once its suspension has
passed and it is not complete. -/
@[instance_reducible] noncomputable def suspension_ready_instance : JobReady Job PState where
  job_ready sched j t := suspension_has_passed sched j t && !completed_by sched j t
  ready_implies_pending sched j t h := by
    have hparts := Bool.and_eq_true_iff.mp h
    have hpassed := Bool.and_eq_true_iff.mp hparts.1
    have harr : job_arrival j + job_suspension j (service sched j t) ≤ t := of_decide_eq_true hpassed.1
    have harr' : job_arrival j ≤ t := Nat.le_trans (Nat.le_add_right _ _) harr
    unfold pending
    simp only [Bool.and_eq_true]
    exact ⟨by unfold Prosa.Behavior.Arrival_sequence.has_arrived; exact decide_eq_true harr', hparts.2⟩

end ReadinessOfSelfSuspendingJobs

section TotalSuspensionTime

variable {Job : JobType} [DecidableEq Job]
variable [JobCost Job] [JobSuspension Job]

/-- The total self-suspension of a job: the sum of its suspensions over all service levels below its cost. -/
def total_suspension (j : Job) : duration :=
  List.foldr Nat.add 0 ((List.range' 0 (job_cost j - 0)).map (job_suspension j))

end TotalSuspensionTime

end Prosa.Model.Readiness.Suspension
