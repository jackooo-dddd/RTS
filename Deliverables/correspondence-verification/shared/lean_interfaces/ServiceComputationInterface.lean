import Prosa.Behavior.Service
import Validation.fixtures.translation_order.ScheduleComputationInterface

namespace Prosa.Validation.ServiceInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}

/-!
The definitions in this block form a small source-shaped computation
interface.  Each production definition below is replaced during export only
after the corresponding *unparameterized* `rfl` guard has been checked by the
Lean kernel and by lean4export's exact-constant guard checker.  Consequently
the imported body remains tied to the actual compiled declaration while its
semantic certificate does not inherit the original Lean proof dependency
graph.
-/

def scheduledAtProjection {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  ProcessorState.scheduled_in PState j (sched t)

noncomputable def serviceAtProjection {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) : work :=
  ProcessorState.service_in PState j (sched t)

noncomputable def receivesServiceAtProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  decide (0 < serviceAtProjection sched j t)

/-- A small, actual-artifact-facing form of the half-open service sum.  The
guard below requires the Lean kernel to accept this body as definitionally
equal to the production `Finset.Ico` implementation. -/
noncomputable def serviceDuringProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t1 t2 : instant) : work :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      serviceAtProjection sched j t

noncomputable def serviceProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) : work :=
  serviceDuringProjection sched j 0 t

noncomputable def completedByProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) [JobCost Job]
    (j : Job) (t : instant) : Bool :=
  decide (job_cost j ≤ serviceProjection sched j t)

noncomputable def completesAtProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) [JobCost Job]
    (j : Job) (t : instant) : Bool :=
  ((!completedByProjection sched j (t - 1) || decide (t = 0)) &&
    completedByProjection sched j t)

noncomputable def jobResponseTimeBoundProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) [JobCost Job] [JobArrival Job]
    (j : Job) (R : duration) : Bool :=
  completedByProjection sched j (job_arrival j + R)

noncomputable def jobMeetsDeadlineProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) [JobCost Job] [JobDeadline Job]
    (j : Job) : Bool :=
  completedByProjection sched j (job_deadline j)

noncomputable def pendingProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) [JobCost Job] [JobArrival Job]
    (j : Job) (t : instant) : Bool :=
  has_arrived j t && !completedByProjection sched j t

noncomputable def pendingEarlierAndAtProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) [JobCost Job] [JobArrival Job]
    (j : Job) (t : instant) : Bool :=
  arrived_before j t && !completedByProjection sched j t

noncomputable def remainingCostProjection
    {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) [JobCost Job]
    (j : Job) (t : instant) : work :=
  job_cost j - serviceProjection sched j t

/-- Exact whole-constant guards consumed by the audited exporter. -/
theorem scheduledAtProjection_guard :
    @scheduled_at = @scheduledAtProjection := rfl
theorem serviceAtProjection_guard :
    @service_at = @serviceAtProjection := rfl
theorem receivesServiceAtProjection_guard :
    @receives_service_at = @receivesServiceAtProjection := rfl
theorem serviceDuringProjection_guard :
    @service_during = @serviceDuringProjection := rfl
theorem serviceProjection_guard :
    @service = @serviceProjection := rfl
theorem completedByProjection_guard :
    @completed_by = @completedByProjection := rfl
theorem completesAtProjection_guard :
    @completes_at = @completesAtProjection := rfl
theorem jobResponseTimeBoundProjection_guard :
    @job_response_time_bound = @jobResponseTimeBoundProjection := rfl
theorem jobMeetsDeadlineProjection_guard :
    @job_meets_deadline = @jobMeetsDeadlineProjection := rfl
theorem pendingProjection_guard :
    @pending = @pendingProjection := rfl
theorem pendingEarlierAndAtProjection_guard :
    @pending_earlier_and_at = @pendingEarlierAndAtProjection := rfl
theorem remainingCostProjection_guard :
    @remaining_cost = @remainingCostProjection := rfl

/-- Exact computation equation for the production wrapper. -/
theorem scheduled_at_eq (sched : schedule PState) (j : Job) (t : instant) :
    scheduled_at sched j t =
      ProcessorState.scheduled_in PState j (sched t) :=
  rfl

/-- Exact computation equation for instantaneous service. -/
theorem service_at_eq (sched : schedule PState) (j : Job) (t : instant) :
    service_at sched j t = ProcessorState.service_in PState j (sched t) :=
  rfl

/-- Exact computation equation for the positive-service Boolean. -/
theorem receives_service_at_eq
    (sched : schedule PState) (j : Job) (t : instant) :
    receives_service_at sched j t = decide (0 < service_at sched j t) :=
  rfl

/-- Exact computation equation for service from time zero. -/
theorem service_eq (sched : schedule PState) (j : Job) (t : instant) :
    service sched j t = service_during sched j 0 t :=
  rfl

variable [JobCost Job] [JobDeadline Job] [JobArrival Job]

theorem completed_by_eq (sched : schedule PState) (j : Job) (t : instant) :
    completed_by sched j t = decide (job_cost j ≤ service sched j t) :=
  rfl

theorem completes_at_eq (sched : schedule PState) (j : Job) (t : instant) :
    completes_at sched j t =
      ((!completed_by sched j (t - 1) || decide (t = 0)) &&
        completed_by sched j t) :=
  rfl

theorem job_response_time_bound_eq
    (sched : schedule PState) (j : Job) (R : duration) :
    job_response_time_bound sched j R =
      completed_by sched j (job_arrival j + R) :=
  rfl

theorem job_meets_deadline_eq (sched : schedule PState) (j : Job) :
    job_meets_deadline sched j = completed_by sched j (job_deadline j) :=
  rfl

theorem pending_eq (sched : schedule PState) (j : Job) (t : instant) :
    pending sched j t = (has_arrived j t && !completed_by sched j t) :=
  rfl

theorem pending_earlier_and_at_eq
    (sched : schedule PState) (j : Job) (t : instant) :
    pending_earlier_and_at sched j t =
      (arrived_before j t && !completed_by sched j t) :=
  rfl

theorem remaining_cost_eq
    (sched : schedule PState) (j : Job) (t : instant) :
    remaining_cost sched j t = job_cost j - service sched j t :=
  rfl

end Prosa.Validation.ServiceInterface
