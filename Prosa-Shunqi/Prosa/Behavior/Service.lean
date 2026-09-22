-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: behavior/service.v

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Prosa.Behavior.Schedule

namespace Prosa.Behavior.Service

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open scoped BigOperators

universe u v w

section Service

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (sched : schedule PState)

/-- Whether job `j` is scheduled at instant `t`. -/
def scheduled_at (j : Job) (t : instant) : Bool :=
  ProcessorState.scheduled_in PState j (sched t)

/-- Instantaneous service received by job `j` at instant `t`. -/
noncomputable def service_at (j : Job) (t : instant) : work :=
  ProcessorState.service_in PState j (sched t)

/-- Boolean observation that job `j` receives positive service at `t`. -/
noncomputable def receives_service_at (j : Job) (t : instant) : Bool :=
  decide (0 < service_at sched j t)

/-- Cumulative service received in the half-open interval `[t1,t2)`. -/
noncomputable def service_during
    (j : Job) (t1 t2 : instant) : work :=
  ∑ t ∈ Finset.Ico t1 t2, service_at sched j t

/-- Cumulative service received up to, but not including, instant `t`. -/
noncomputable def service (j : Job) (t : instant) : work :=
  service_during sched j 0 t

variable [JobCost Job]
variable [JobDeadline Job]
variable [JobArrival Job]

/-- Boolean observation that `j` has received its required execution cost by
instant `t`. -/
noncomputable def completed_by (j : Job) (t : instant) : Bool :=
  decide (job_cost j ≤ service sched j t)

/-- The exact v0.6 completion predicate.  At time zero the predecessor test
is bypassed by the explicit Boolean equality disjunct. -/
noncomputable def completes_at (j : Job) (t : instant) : Bool :=
  (!completed_by sched j (t - 1) || decide (t = 0)) &&
    completed_by sched j t

/-- Boolean response-time-bound observation for job `j`. -/
noncomputable def job_response_time_bound (j : Job) (R : duration) : Bool :=
  completed_by sched j (job_arrival j + R)

/-- Boolean observation that job `j` completes by its absolute deadline. -/
noncomputable def job_meets_deadline (j : Job) : Bool :=
  completed_by sched j (job_deadline j)

/-- Boolean observation that `j` has arrived but has not yet completed. -/
noncomputable def pending (j : Job) (t : instant) : Bool :=
  has_arrived j t && !completed_by sched j t

/-- Boolean observation that `j` arrived strictly before `t` and remains
incomplete at `t`. -/
noncomputable def pending_earlier_and_at (j : Job) (t : instant) : Bool :=
  arrived_before j t && !completed_by sched j t

/-- Remaining execution cost, using truncated natural subtraction. -/
noncomputable def remaining_cost (j : Job) (t : instant) : work :=
  job_cost j - service sched j t

end Service

end Prosa.Behavior.Service
