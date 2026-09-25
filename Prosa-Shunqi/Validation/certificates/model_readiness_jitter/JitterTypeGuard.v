From mathcomp Require Import ssreflect ssrbool eqtype.
From prosa Require Import model.readiness.jitter.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJitterPublic.

(** Exact elaborated public signatures, from the official source and the
    actual imported Lean artifact. These fail if either boundary drifts. *)
Definition ji_source_class_type_guard : JobType -> Type :=
  @prosa.model.readiness.jitter.JobJitter.

Definition ji_source_release_type_guard :
    forall (Job : JobType),
      prosa.behavior.job.JobArrival Job ->
      prosa.model.readiness.jitter.JobJitter Job ->
      Job -> instant -> bool :=
  @prosa.model.readiness.jitter.is_released.

Definition ji_source_helper_type_guard :
    forall (Job : JobType) (PState : ProcessorState Job)
      (ar : prosa.behavior.job.JobArrival Job)
      (cost : prosa.behavior.job.JobCost Job),
      prosa.model.readiness.jitter.JobJitter Job ->
      @prosa.behavior.ready.JobReady Job PState cost ar :=
  @prosa.model.readiness.jitter.jitter_ready_instance.

Definition ji_target_class_type_guard :
    forall (Job : ImportedJitterPublic.Prosa_Behavior_Job_JobType),
      ImportedJitterPublic.DecidableEq Job -> Type :=
  @ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter.

Definition ji_target_release_type_guard :
    forall (Job : ImportedJitterPublic.Prosa_Behavior_Job_JobType)
      (d : ImportedJitterPublic.DecidableEq Job),
      ImportedJitterPublic.Prosa_Behavior_Job_JobArrival Job d ->
      ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter Job d ->
      Job -> ImportedJitterPublic.Prosa_Behavior_Time_instant ->
      ImportedJitterPublic.Bool :=
  @ImportedJitterPublic.Prosa_Model_Readiness_Jitter_is_released.

Definition ji_target_ready_bool_type_guard :
    ImportedJitterPublic.Bool -> ImportedJitterPublic.Bool ->
      ImportedJitterPublic.Bool :=
  @ImportedJitterPublic.Prosa_Model_Readiness_Jitter_jitter_ready_bool.

Print Assumptions ji_source_class_type_guard.
Print Assumptions ji_source_release_type_guard.
Print Assumptions ji_source_helper_type_guard.
Print Assumptions ji_target_class_type_guard.
Print Assumptions ji_target_release_type_guard.
Print Assumptions ji_target_ready_bool_type_guard.
