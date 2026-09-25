From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import model.readiness.basic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessBasicProjection.

Module I := ImportedReadinessBasicProjection.

(** Rank 55 has no public declarations in the v0.6 inventory.  This named
    local instance is nevertheless used explicitly by downstream source files.
    These guards certify its source and imported-target interface and its
    ready/pending computation without assuming either result. *)

Section SourceInterface.
  Context {Job : prosa.behavior.job.JobType}.
  Context {PState : prosa.behavior.schedule.ProcessorState Job}.
  Context {arrival : prosa.behavior.job.JobArrival Job}.
  Context {cost : prosa.behavior.job.JobCost Job}.

  Definition source_basic_ready_exact_type :
      @prosa.behavior.ready.JobReady Job PState cost arrival :=
    @prosa.model.readiness.basic.basic_ready_instance
      Job PState arrival cost.

  Lemma source_basic_ready_field
      (sched : prosa.behavior.schedule.schedule PState)
      (j : Job) (t : prosa.behavior.time.instant) :
    @prosa.behavior.ready.job_ready Job PState cost arrival
      source_basic_ready_exact_type sched j t =
    @prosa.behavior.service.pending Job PState sched cost arrival j t.
  Proof. by []. Qed.

  Lemma source_basic_ready_law
      (sched : prosa.behavior.schedule.schedule PState)
      (j : Job) (t : prosa.behavior.time.instant) :
    @prosa.behavior.ready.job_ready Job PState cost arrival
      source_basic_ready_exact_type sched j t ->
    @prosa.behavior.service.pending Job PState sched cost arrival j t.
  Proof. by []. Qed.
End SourceInterface.

Section ImportedTargetInterface.
  Context (Job : I.Prosa_Behavior_Job_JobType).
  Context (dec : I.DecidableEq Job).
  Context (PState : I.Prosa_Behavior_Schedule_ProcessorState Job dec).
  Context (arrival : I.Prosa_Behavior_Job_JobArrival Job dec).
  Context (cost : I.Prosa_Behavior_Job_JobCost Job dec).

  Definition target_basic_ready_exact_type :
      I.Prosa_Behavior_Ready_JobReady Job dec PState cost arrival :=
    I.Prosa_Model_Readiness_Basic_basic_ready_instance
      Job dec PState arrival cost.

  Lemma target_basic_ready_field_projection
      (sched : I.Prosa_Behavior_Schedule_schedule Job dec PState)
      (j : Job) (t : I.Prosa_Behavior_Time_instant) :
    I.Prosa_Behavior_Ready_JobReady_job_ready
      Job dec PState cost arrival target_basic_ready_exact_type sched j t =
    I.Prosa_Validation_ServiceInterface_pendingProjection
      Job dec PState sched cost arrival j t.
  Proof. reflexivity. Qed.

  Lemma target_basic_ready_field_pending
      (sched : I.Prosa_Behavior_Schedule_schedule Job dec PState)
      (j : Job) (t : I.Prosa_Behavior_Time_instant) :
    I.Prosa_Behavior_Ready_JobReady_job_ready
      Job dec PState cost arrival target_basic_ready_exact_type sched j t =
    I.Prosa_Behavior_Service_pending
      Job dec PState sched cost arrival j t.
  Proof. reflexivity. Qed.

  Lemma target_basic_ready_law
      (sched : I.Prosa_Behavior_Schedule_schedule Job dec PState)
      (j : Job) (t : I.Prosa_Behavior_Time_instant) :
    Lean.eq
      (I.Prosa_Behavior_Ready_JobReady_job_ready
        Job dec PState cost arrival target_basic_ready_exact_type sched j t)
      I.Bool_true ->
    Lean.eq (I.Prosa_Behavior_Service_pending
      Job dec PState sched cost arrival j t) I.Bool_true.
  Proof.
    intro h.
    exact h.
  Qed.
End ImportedTargetInterface.

Goal True.
Proof.
  idtac "AUDIT_BEGIN source_exact_type".
  Print Assumptions source_basic_ready_exact_type.
  idtac "AUDIT_END source_exact_type".
  idtac "AUDIT_BEGIN source_field".
  Print Assumptions source_basic_ready_field.
  idtac "AUDIT_END source_field".
  idtac "AUDIT_BEGIN source_law".
  Print Assumptions source_basic_ready_law.
  idtac "AUDIT_END source_law".
  idtac "AUDIT_BEGIN target_exact_type".
  Print Assumptions target_basic_ready_exact_type.
  idtac "AUDIT_END target_exact_type".
  idtac "AUDIT_BEGIN target_field_projection".
  Print Assumptions target_basic_ready_field_projection.
  idtac "AUDIT_END target_field_projection".
  idtac "AUDIT_BEGIN target_field_pending".
  Print Assumptions target_basic_ready_field_pending.
  idtac "AUDIT_END target_field_pending".
  idtac "AUDIT_BEGIN target_law".
  Print Assumptions target_basic_ready_law.
  idtac "AUDIT_END target_law".
Abort.
