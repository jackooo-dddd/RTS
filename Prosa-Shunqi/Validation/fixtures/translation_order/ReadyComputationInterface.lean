import Prosa.Behavior.Ready
import Validation.fixtures.translation_order.ServiceComputationInterface
import Validation.fixtures.translation_order.BigcatComputationInterface

namespace Prosa.Validation.ReadyInterface

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

def backloggedProjection {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobCost Job] [JobArrival Job]
    [JobReady Job PState]
    (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  job_ready sched j t && !scheduled_at sched j t

def jobsComeFromArrivalSequenceProjection
    {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    (arrSeq : arrival_sequence Job) : Prop :=
  ∀ j t, scheduled_at sched j t = true → arrives_in arrSeq j

def jobsMustArriveToExecuteProjection
    {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (sched : schedule PState) : Prop :=
  ∀ j t, scheduled_at sched j t = true → has_arrived j t = true

def jobsMustBeReadyToExecuteProjection
    {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobReady Job PState] : Prop :=
  ∀ j t, scheduled_at sched j t = true → job_ready sched j t = true

noncomputable def completedJobsDontExecuteProjection
    {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] : Prop :=
  ∀ j t, scheduled_at sched j t = true → service sched j t < job_cost j

def validScheduleProjection
    {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobReady Job PState]
    (arrSeq : arrival_sequence Job) : Prop :=
  jobsComeFromArrivalSequenceProjection sched arrSeq ∧
    jobsMustBeReadyToExecuteProjection sched

theorem backloggedProjection_guard :
    @backlogged = @backloggedProjection := rfl
theorem jobsComeFromArrivalSequenceProjection_guard :
    @jobs_come_from_arrival_sequence =
      @jobsComeFromArrivalSequenceProjection := rfl
theorem jobsMustArriveToExecuteProjection_guard :
    @jobs_must_arrive_to_execute = @jobsMustArriveToExecuteProjection := rfl
theorem jobsMustBeReadyToExecuteProjection_guard :
    @jobs_must_be_ready_to_execute =
      @jobsMustBeReadyToExecuteProjection := rfl
theorem completedJobsDontExecuteProjection_guard :
    @completed_jobs_dont_execute = @completedJobsDontExecuteProjection := rfl
theorem validScheduleProjection_guard :
    @valid_schedule = @validScheduleProjection := rfl

end Prosa.Validation.ReadyInterface
