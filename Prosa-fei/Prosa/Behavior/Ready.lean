-- Translated from: ../rt-proofs/behavior/ready.v
import Prosa.Behavior.Service

namespace Prosa.Behavior.Ready

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence

class JobReady (Job : JobType) (PState : Type _)
    [ProcessorState Job PState] [JobCost Job] [JobArrival Job] where
  job_ready : schedule PState → Job → instant → Bool
  ready_implies_pending :
    ∀ sched j t, job_ready sched j t = true → pending sched j t

export JobReady (job_ready)

section Backlogged

variable {Job : JobType} {PState : Type _}
variable [ProcessorState Job PState]
variable [JobCost Job] [JobArrival Job]
variable [JobReady Job PState]

noncomputable def backlogged (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  job_ready sched j t && ! scheduled_at sched j t

end Backlogged

section ValidSchedule

variable {Job : JobType} {PState : Type _}
variable [ProcessorState Job PState]
variable [JobArrival Job]

def jobs_come_from_arrival_sequence (sched : schedule PState) (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j t, scheduled_at sched j t = true → arrives_in arr_seq j

def jobs_must_arrive_to_execute (sched : schedule PState) : Prop :=
  ∀ (j : Job) t, scheduled_at sched j t = true → has_arrived j t

variable [JobCost Job]
variable [JobReady Job PState]

def jobs_must_be_ready_to_execute (sched : schedule PState) : Prop :=
  ∀ (j : Job) t, scheduled_at sched j t = true → job_ready sched j t = true

noncomputable def completed_jobs_dont_execute (sched : schedule PState) : Prop :=
  ∀ (j : Job) t, scheduled_at sched j t = true → service sched j t < job_cost j

def valid_schedule (sched : schedule PState) (arr_seq : arrival_sequence Job) : Prop :=
  jobs_come_from_arrival_sequence sched arr_seq ∧
  jobs_must_be_ready_to_execute (Job := Job) sched

end ValidSchedule

end Prosa.Behavior.Ready
