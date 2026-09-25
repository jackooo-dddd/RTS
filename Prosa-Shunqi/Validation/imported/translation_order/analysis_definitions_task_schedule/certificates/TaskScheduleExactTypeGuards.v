From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.definitions.task_schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskSchedule.

(** Both signatures are elaborated afresh from the pinned source and the
    actual imported Lean artifact; no postulated type equality is used. *)
Definition TsSourceSig
    (Result : prosa.behavior.job.JobType -> Type) : Type :=
  forall (Task : prosa.model.task.concept.TaskType)
    (Job : prosa.behavior.job.JobType),
    prosa.model.task.concept.JobTask Job Task ->
    prosa.behavior.arrival_sequence.arrival_sequence Job ->
    forall (PState : prosa.behavior.schedule.ProcessorState Job),
    @prosa.behavior.schedule.schedule Job PState ->
    Task -> Result Job.

Definition TsTargetSig
    (Result : ImportedTaskSchedule.Prosa_Behavior_Job_JobType -> Type) : Type :=
  forall (Task : ImportedTaskSchedule.Prosa_Model_Task_Concept_TaskType)
    (deqTask : ImportedTaskSchedule.DecidableEq Task)
    (Job : ImportedTaskSchedule.Prosa_Behavior_Job_JobType)
    (deqJob : ImportedTaskSchedule.DecidableEq Job),
    ImportedTaskSchedule.Prosa_Model_Task_Concept_JobTask
      Job deqJob Task deqTask ->
    forall (PState : ImportedTaskSchedule.Prosa_Behavior_Schedule_ProcessorState
      Job deqJob),
    ImportedTaskSchedule.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job deqJob ->
    ImportedTaskSchedule.Prosa_Behavior_Schedule_schedule
      Job deqJob PState ->
    Task -> Result Job.

Check (@prosa.analysis.definitions.task_schedule.scheduled_jobs_of_task_at :
  TsSourceSig (fun Job => prosa.behavior.time.instant -> seq Job)).
Check (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_scheduled_jobs_of_task_at :
  TsTargetSig (fun Job =>
    ImportedTaskSchedule.Prosa_Behavior_Time_instant ->
    ImportedTaskSchedule.List Job)).

Check (@prosa.analysis.definitions.task_schedule.task_scheduled_at :
  TsSourceSig (fun _ => prosa.behavior.time.instant -> bool)).
Check (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at :
  TsTargetSig (fun _ =>
    ImportedTaskSchedule.Prosa_Behavior_Time_instant ->
    ImportedTaskSchedule.Bool)).

Check (@prosa.analysis.definitions.task_schedule.task_service_at :
  TsSourceSig (fun _ => prosa.behavior.time.instant -> nat)).
Check (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service_at :
  TsTargetSig (fun _ =>
    ImportedTaskSchedule.Prosa_Behavior_Time_instant ->
    ImportedTaskSchedule.Prosa_Behavior_Job_work)).

Check (@prosa.analysis.definitions.task_schedule.task_service_during :
  TsSourceSig (fun _ => prosa.behavior.time.instant ->
    prosa.behavior.time.instant -> nat)).
Check (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service_during :
  TsTargetSig (fun _ =>
    ImportedTaskSchedule.Prosa_Behavior_Time_instant ->
    ImportedTaskSchedule.Prosa_Behavior_Time_instant ->
    ImportedTaskSchedule.Prosa_Behavior_Job_work)).

Check (@prosa.analysis.definitions.task_schedule.task_service :
  TsSourceSig (fun _ => prosa.behavior.time.instant -> nat)).
Check (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service :
  TsTargetSig (fun _ =>
    ImportedTaskSchedule.Prosa_Behavior_Time_instant ->
    ImportedTaskSchedule.Prosa_Behavior_Job_work)).

Check (@prosa.analysis.definitions.task_schedule.served_jobs_of_task_at :
  TsSourceSig (fun Job => prosa.behavior.time.instant -> seq Job)).
Check (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_served_jobs_of_task_at :
  TsTargetSig (fun Job =>
    ImportedTaskSchedule.Prosa_Behavior_Time_instant ->
    ImportedTaskSchedule.List Job)).

Check (@prosa.analysis.definitions.task_schedule.task_served_at :
  TsSourceSig (fun _ => prosa.behavior.time.instant -> bool)).
Check (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_served_at :
  TsTargetSig (fun _ =>
    ImportedTaskSchedule.Prosa_Behavior_Time_instant ->
    ImportedTaskSchedule.Bool)).
