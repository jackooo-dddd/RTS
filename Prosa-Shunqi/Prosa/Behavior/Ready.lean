-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: behavior/ready.v

import Prosa.Behavior.Service

namespace Prosa.Behavior.Ready

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u v w

/-- A v0.6 readiness model.  The law preserves the source requirement that
every ready job is pending. -/
class JobReady (Job : JobType) [DecidableEq Job]
    (PState : ProcessorState Job) [JobCost Job] [JobArrival Job] where
  job_ready : schedule PState → Job → instant → Bool
  ready_implies_pending :
    ∀ sched j t, job_ready sched j t = true → pending sched j t = true

export JobReady (job_ready ready_implies_pending)

section Backlogged

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable [JobCost Job] [JobArrival Job] [JobReady Job PState]

/-- A job is backlogged iff it is ready but not scheduled. -/
def backlogged (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  job_ready sched j t && !scheduled_at sched j t

end Backlogged

section ValidSchedule

variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job]
variable {PState : ProcessorState Job}
variable (sched : schedule PState)

/-- Every scheduled job occurs in the supplied arrival sequence. -/
def jobs_come_from_arrival_sequence (arrSeq : arrival_sequence Job) : Prop :=
  ∀ j t, scheduled_at sched j t = true → arrives_in arrSeq j

/-- Scheduled jobs must already have arrived. -/
def jobs_must_arrive_to_execute : Prop :=
  ∀ j t, scheduled_at sched j t = true → has_arrived j t = true

variable [JobCost Job] [JobReady Job PState]

/-- Scheduled jobs must be ready. -/
def jobs_must_be_ready_to_execute : Prop :=
  ∀ j t, scheduled_at sched j t = true → job_ready sched j t = true

/-- A completed job receives no further execution. -/
noncomputable def completed_jobs_dont_execute : Prop :=
  ∀ j t, scheduled_at sched j t = true → service sched j t < job_cost j

/-- Source-exact v0.6 validity contract. -/
def valid_schedule (arrSeq : arrival_sequence Job) : Prop :=
  jobs_come_from_arrival_sequence sched arrSeq ∧
    jobs_must_be_ready_to_execute sched

end ValidSchedule

end Prosa.Behavior.Ready
