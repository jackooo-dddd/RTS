From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From prosa Require Import model.schedule.nonpreemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedNonpreemptive.

(** Exact elaborated signatures of the official v0.6 declaration and the
    actual imported Lean definition.  Both guards fail on interface drift. *)
Definition nps_source_type_guard :
    forall (Job : prosa.behavior.job.JobType),
      prosa.behavior.job.JobCost Job ->
      forall (PState : prosa.behavior.schedule.ProcessorState Job),
        prosa.behavior.schedule.schedule PState -> Prop :=
  @prosa.model.schedule.nonpreemptive.nonpreemptive_schedule.

Definition nps_target_type_guard :
    forall (Job : ImportedNonpreemptive.Prosa_Behavior_Job_JobType)
      (d : ImportedNonpreemptive.DecidableEq Job),
      ImportedNonpreemptive.Prosa_Behavior_Job_JobCost Job d ->
      forall (PState : ImportedNonpreemptive.Prosa_Behavior_Schedule_ProcessorState
          Job d),
        ImportedNonpreemptive.Prosa_Behavior_Schedule_schedule Job d PState ->
        SProp :=
  @ImportedNonpreemptive.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule.

Print Assumptions nps_source_type_guard.
Print Assumptions nps_target_type_guard.
