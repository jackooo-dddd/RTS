From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.definitions.job_response_time.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJobResponseTime.

(** Elaborated source and actual compiled target types; these checks are
    separate from the proof of semantic correspondence. *)
Check (@prosa.analysis.definitions.job_response_time.job_response_time_exceeds :
  forall (Job : prosa.behavior.job.JobType),
    prosa.behavior.job.JobCost Job ->
    prosa.behavior.job.JobArrival Job ->
    forall (PState : prosa.behavior.schedule.ProcessorState Job),
      @prosa.behavior.schedule.schedule Job PState ->
      Job -> prosa.behavior.time.duration -> bool).

Check (ImportedJobResponseTime.Prosa_Analysis_Definitions_JobResponseTime_job_response_time_exceeds :
  forall (Job : ImportedJobResponseTime.Prosa_Behavior_Job_JobType)
    (deq : ImportedJobResponseTime.DecidableEq Job),
    ImportedJobResponseTime.Prosa_Behavior_Job_JobCost Job deq ->
    ImportedJobResponseTime.Prosa_Behavior_Job_JobArrival Job deq ->
    forall (PState : ImportedJobResponseTime.Prosa_Behavior_Schedule_ProcessorState Job deq),
      ImportedJobResponseTime.Prosa_Behavior_Schedule_schedule Job deq PState ->
      Job -> ImportedJobResponseTime.Prosa_Behavior_Time_duration ->
      ImportedJobResponseTime.Bool).
