From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From prosa Require Import model.schedule.work_conserving.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedWorkConserving.

(** Full elaborated public types: source has no equality-instance binder,
    target includes its explicit DecidableEq binder.  These definitions fail
    to elaborate if either source or imported target interface drifts. *)
Definition wc_source_work_conserving_type_guard :
    forall (Job : prosa.behavior.job.JobType)
      (arrival : prosa.behavior.job.JobArrival Job)
      (cost : prosa.behavior.job.JobCost Job)
      (PState : prosa.behavior.schedule.ProcessorState Job),
      @prosa.behavior.ready.JobReady Job PState cost arrival ->
      prosa.behavior.arrival_sequence.arrival_sequence Job ->
      prosa.behavior.schedule.schedule PState -> Prop :=
  @prosa.model.schedule.work_conserving.work_conserving.

Definition wc_source_jobs_backlogged_at_type_guard :
    forall (Job : prosa.behavior.job.JobType)
      (arrival : prosa.behavior.job.JobArrival Job)
      (cost : prosa.behavior.job.JobCost Job)
      (PState : prosa.behavior.schedule.ProcessorState Job),
      @prosa.behavior.ready.JobReady Job PState cost arrival ->
      prosa.behavior.arrival_sequence.arrival_sequence Job ->
      prosa.behavior.schedule.schedule PState -> nat -> seq Job :=
  @prosa.model.schedule.work_conserving.jobs_backlogged_at.

Definition wc_target_work_conserving_type_guard :
    forall (Job : ImportedWorkConserving.Prosa_Behavior_Job_JobType)
      (d : ImportedWorkConserving.DecidableEq Job)
      (arrival : ImportedWorkConserving.Prosa_Behavior_Job_JobArrival Job d)
      (cost : ImportedWorkConserving.Prosa_Behavior_Job_JobCost Job d)
      (PState : ImportedWorkConserving.Prosa_Behavior_Schedule_ProcessorState
        Job d),
      ImportedWorkConserving.Prosa_Behavior_Ready_JobReady Job d PState
        cost arrival ->
      ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrival_sequence
        Job d ->
      ImportedWorkConserving.Prosa_Behavior_Schedule_schedule Job d PState ->
      SProp :=
  @ImportedWorkConserving.Prosa_Model_Schedule_WorkConserving_work_conserving.

Definition wc_target_jobs_backlogged_at_type_guard :
    forall (Job : ImportedWorkConserving.Prosa_Behavior_Job_JobType)
      (d : ImportedWorkConserving.DecidableEq Job)
      (arrival : ImportedWorkConserving.Prosa_Behavior_Job_JobArrival Job d)
      (cost : ImportedWorkConserving.Prosa_Behavior_Job_JobCost Job d)
      (PState : ImportedWorkConserving.Prosa_Behavior_Schedule_ProcessorState
        Job d),
      ImportedWorkConserving.Prosa_Behavior_Ready_JobReady Job d PState
        cost arrival ->
      ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrival_sequence
        Job d ->
      ImportedWorkConserving.Prosa_Behavior_Schedule_schedule Job d PState ->
      Lean.Nat -> ImportedWorkConserving.List Job :=
  @ImportedWorkConserving.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at.

Print Assumptions wc_source_work_conserving_type_guard.
Print Assumptions wc_source_jobs_backlogged_at_type_guard.
Print Assumptions wc_target_work_conserving_type_guard.
Print Assumptions wc_target_jobs_backlogged_at_type_guard.
