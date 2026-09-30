(* Copy of the accepted certificates/model_readiness_suspension/SuspensionCorrespondence.v, re-bound to this
   export; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import SuspensionSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedDynamicSuspension ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations ProgressHelpers.

Module I := ImportedDynamicSuspension.
Module S := SuspensionSemanticSource.SuspensionSemanticSource.

(** Correspondences for [model/readiness/suspension.v].  The class
    [JobSuspension] (a definitional class: a function from jobs and service
    levels to durations) is related pointwise, with the service levels and
    durations related by [SubNatRel]; every source instance has a related
    compiled instance and conversely.  For related processor states
    (two-sided [SvcProcessorStateRel]), schedules, job arrivals, job costs and
    suspension instances, the three extracted source definitions and the
    compiled Lean definitions are related.  Service and [no_progress_for] are
    the accepted progress helpers re-bound to this artifact. *)

Lemma susp_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Definition susp_import_fun (fR : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun n => sub_nat_to_imported (fR (sub_nat_to_rocq n)).
Definition susp_export_fun (fL : Lean.Nat -> Lean.Nat) : nat -> nat :=
  fun n => sub_nat_to_rocq (fL (sub_nat_to_imported n)).

Lemma susp_import_fun_rel fR : SubNatFunRel fR (susp_import_fun fR).
Proof.
  intros nR nL Hn. unfold SubNatRel, susp_import_fun.
  rewrite (susp_nat_input nR nL Hn). exact (@Lean.eq_refl _ _).
Qed.

Lemma susp_export_fun_rel fL : SubNatFunRel (susp_export_fun fL) fL.
Proof.
  intros nR nL Hn. unfold SubNatRel, susp_export_fun.
  exact (sub_imported_eq_trans _ _ _ (sub_nat_imported_roundtrip _)
    (sub_imported_eq_congr fL _ _ Hn)).
Qed.

Section Suspension.
  Context (Job : eqType).
  Let dJ := svc_decidable_eq Job.

  Definition SuspJobSuspensionRel (sR : S.JobSuspension Job)
      (sL : I.Prosa_Model_Readiness_Suspension_JobSuspension Job dJ) : SProp :=
    forall j : Job, SubNatFunRel (@S.job_suspension Job sR j)
      (I.Prosa_Model_Readiness_Suspension_JobSuspension_job_suspension Job dJ sL j).

  Lemma JobSuspension_source_total (sR : S.JobSuspension Job) :
    SuspJobSuspensionRel sR
      (I.Prosa_Model_Readiness_Suspension_JobSuspension_mk Job dJ
        (fun j => susp_import_fun (@S.job_suspension Job sR j))).
  Proof. intro j. exact (susp_import_fun_rel _). Qed.

  Lemma JobSuspension_target_total
      (sL : I.Prosa_Model_Readiness_Suspension_JobSuspension Job dJ) :
    SuspJobSuspensionRel
      ((fun j => susp_export_fun
        (I.Prosa_Model_Readiness_Suspension_JobSuspension_job_suspension Job dJ sL j))
        : S.JobSuspension Job) sL.
  Proof. intro j. exact (susp_export_fun_rel _). Qed.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : SvcJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable sR : S.JobSuspension Job.
  Variable sL : I.Prosa_Model_Readiness_Suspension_JobSuspension Job dJ.
  Hypothesis Hs : SuspJobSuspensionRel sR sL.

  Lemma susp_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
      (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j)
      (pg_service_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
  Qed.

  Lemma susp_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR)
      (I.Prosa_Behavior_Service_pending Job dJ PStateL schedL costL jaL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending.
    cbn [I.Prosa_Behavior_Service_pending].
    exact (svc_bool_and_related _ _ _ _ (svc_has_arrived_related Job jaR jaL j Hja tR tL Ht)
      (svc_bool_not_related _ _ (susp_completed_by_related j tR tL Ht))).
  Qed.

  Theorem suspension_has_passed_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@S.suspension_has_passed Job PStateR jaR sR schedR j tR)
      (I.Prosa_Model_Readiness_Suspension_suspension_has_passed Job dJ PStateL jaL sL
        schedL j tL).
  Proof.
    intro Ht. unfold S.suspension_has_passed.
    cbn [I.Prosa_Model_Readiness_Suspension_suspension_has_passed].
    have Hd := Hs j _ _ (pg_service_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht).
    exact (svc_bool_and_related _ _ _ _
      (svc_decide_le_related _ _ _ _ (svc_target_add_related _ _ _ _ (Hja j) Hd) Ht)
      (no_progress_for_correspondence Job PStateR PStateL R schedR schedL Hsched j _ _ _ _ Ht Hd)).
  Qed.

  Theorem suspended_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@S.suspended Job PStateR jaR costR sR schedR j tR)
      (I.Prosa_Model_Readiness_Suspension_suspended Job dJ PStateL jaL costL sL schedL j tL).
  Proof.
    intro Ht. unfold S.suspended.
    cbn [I.Prosa_Model_Readiness_Suspension_suspended].
    exact (svc_bool_and_related _ _ _ _
      (svc_bool_not_related _ _ (suspension_has_passed_correspondence j tR tL Ht))
      (susp_pending_related j tR tL Ht)).
  Qed.

  Theorem total_suspension_correspondence (j : Job) :
    SubNatRel (@S.total_suspension Job costR sR j)
      (I.Prosa_Model_Readiness_Suspension_total_suspension Job dJ costL sL j).
  Proof.
    unfold S.total_suspension.
    cbn [I.Prosa_Model_Readiness_Suspension_total_suspension].
    exact (svc_interval_sum_related O (@prosa.behavior.job.job_cost Job costR j)
      Lean.Nat_zero _ _ _ (sub_nat_rel_canonical O) (Hcost j) (Hs j)).
  Qed.
End Suspension.

