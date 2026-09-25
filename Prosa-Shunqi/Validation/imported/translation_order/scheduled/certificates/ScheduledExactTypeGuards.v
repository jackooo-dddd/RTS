From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.schedule.scheduled.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduledFull.

Check (@prosa.model.schedule.scheduled.scheduled_jobs_at :
  forall (Job : prosa.behavior.job.JobType)
    (PState : prosa.behavior.schedule.ProcessorState Job),
    prosa.behavior.arrival_sequence.arrival_sequence Job ->
    @prosa.behavior.schedule.schedule Job PState ->
    prosa.behavior.time.instant -> seq Job).
Check (ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at :
  forall (Job : ImportedScheduledFull.Prosa_Behavior_Job_JobType)
    (deq : ImportedScheduledFull.DecidableEq Job)
    (PState : ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState
      Job deq),
    ImportedScheduledFull.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job deq ->
    ImportedScheduledFull.Prosa_Behavior_Schedule_schedule Job deq PState ->
    ImportedScheduledFull.Prosa_Behavior_Time_instant ->
    ImportedScheduledFull.List Job).

Check (@prosa.model.schedule.scheduled.scheduled_job_at :
  forall (Job : prosa.behavior.job.JobType)
    (PState : prosa.behavior.schedule.ProcessorState Job),
    prosa.behavior.arrival_sequence.arrival_sequence Job ->
    @prosa.behavior.schedule.schedule Job PState ->
    prosa.behavior.time.instant -> option Job).
Check (ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_scheduled_job_at :
  forall (Job : ImportedScheduledFull.Prosa_Behavior_Job_JobType)
    (deq : ImportedScheduledFull.DecidableEq Job)
    (PState : ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState
      Job deq),
    ImportedScheduledFull.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job deq ->
    ImportedScheduledFull.Prosa_Behavior_Schedule_schedule Job deq PState ->
    ImportedScheduledFull.Prosa_Behavior_Time_instant ->
    ImportedScheduledFull.Option Job).

Check (@prosa.model.schedule.scheduled.is_idle :
  forall (Job : prosa.behavior.job.JobType)
    (PState : prosa.behavior.schedule.ProcessorState Job),
    prosa.behavior.arrival_sequence.arrival_sequence Job ->
    @prosa.behavior.schedule.schedule Job PState ->
    prosa.behavior.time.instant -> bool).
Check (ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_is_idle :
  forall (Job : ImportedScheduledFull.Prosa_Behavior_Job_JobType)
    (deq : ImportedScheduledFull.DecidableEq Job)
    (PState : ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState
      Job deq),
    ImportedScheduledFull.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job deq ->
    ImportedScheduledFull.Prosa_Behavior_Schedule_schedule Job deq PState ->
    ImportedScheduledFull.Prosa_Behavior_Time_instant ->
    ImportedScheduledFull.Bool).
