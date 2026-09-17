-- Translated from: ../rt-proofs/behavior/service.v
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals

import Prosa.Behavior.Schedule

namespace Prosa.Behavior.Service

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule

section Service

variable {Job : JobType} {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)

/-- Whether a job j is scheduled at time t. -/
noncomputable def scheduled_at (j : Job) (t : instant) : Bool :=
  ProcessorState.scheduled_in j (sched t)

/-- The instantaneous service received by job j at time t. -/
def service_at (j : Job) (t : instant) : work :=
  ProcessorState.service_in j (sched t)

/-- The cumulative service received by job j during any interval [t1, t2). -/
noncomputable def service_during (j : Job) (t1 t2 : instant) : work :=
  ∑ t ∈ Finset.Ico t1 t2, service_at sched j t

/-- The cumulative service received by job j up to (but not including) time t. -/
noncomputable def service (j : Job) (t : instant) : work :=
  service_during sched j 0 t

variable [JobCost Job]
variable [JobDeadline Job]
variable [JobArrival Job]

/-- Job j has completed by time t if it received all required service. -/
noncomputable def completed_by (j : Job) (t : instant) : Prop :=
  service sched j t ≥ job_cost j

/-- Job j completes at time t if it has completed by time t but not by time t - 1. -/
noncomputable def completes_at (j : Job) (t : instant) : Prop :=
  ¬ completed_by sched j (t - 1) ∧ completed_by sched j t

/-- R is a response time bound of job j if j has completed by R units after its arrival. -/
noncomputable def job_response_time_bound (j : Job) (R : duration) : Prop :=
  completed_by sched j (job_arrival j + R)

/-- Job j meets its deadline if it completes by its absolute deadline. -/
noncomputable def job_meets_deadline (j : Job) : Prop :=
  completed_by sched j (job_deadline j)

/-- Job j is pending at time t iff it has arrived but has not yet completed. -/
noncomputable def pending (j : Job) (t : instant) : Prop :=
  Prosa.Behavior.Arrival_sequence.has_arrived j t ∧ ¬ completed_by sched j t

/-- Job j is pending earlier and at time t iff it has arrived before time t
    and has not been completed yet. -/
noncomputable def pending_earlier_and_at (j : Job) (t : instant) : Prop :=
  Prosa.Behavior.Arrival_sequence.arrived_before j t ∧ ¬ completed_by sched j t

/-- The remaining cost of job j at time t. -/
noncomputable def remaining_cost (j : Job) (t : instant) : work :=
  job_cost j - service sched j t

end Service

end Prosa.Behavior.Service
