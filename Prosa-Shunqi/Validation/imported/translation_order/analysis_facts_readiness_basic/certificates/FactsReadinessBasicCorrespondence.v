From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsReadinessBasicSemanticSource.
From prosa Require Import model.readiness.basic analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsReadinessBasic ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence
  ReadinessCorrespondence.

Module I := ImportedFactsReadinessBasic.
Module S := FactsReadinessBasicSemanticSource.FactsReadinessBasicSemanticSource.

(** Statement correspondences for [analysis/facts/readiness/basic.v].

    Source side: the extracted statements [S.statement_X] (elaborated with
    the source's section-local basic readiness instance) specialised at their
    leading inputs; target side: the imported Lean theorem types, which pass
    the accepted Lean [basic_ready_instance] explicitly.  The two basic
    readiness models are related by the accepted [RdJobReadyRel] (both are
    [pending]).  Inputs: [job_arrival] by [ArJobArrivalRel], [job_cost] by
    [SvcJobCostRel], processor states and schedules by the accepted two-sided
    relations, arrival sequences by [ArArrivalSequenceRel], the JLFP policy
    pointwise on Booleans.  Nonclairvoyance is closed by the accepted
    readiness certificate.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section Basic.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Lemma frb_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at].
      exact (svc_scheduled_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma frb_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
        (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.completed_by.
      cbn [I.Prosa_Behavior_Service_completed_by].
      exact (svc_decide_le_related _ _ _ _ (Hcost j)
        (rd_service_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
    Qed.

    Lemma frb_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR)
        (I.Prosa_Behavior_Service_pending Job dJ PStateL schedL costL jaL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.pending.
      cbn [I.Prosa_Behavior_Service_pending].
      apply ar_bool_and_related.
      - exact (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht).
      - exact (svc_bool_not_related _ _ (frb_completed_by_related j tR tL Ht)).
    Qed.
  End Sched.

  Lemma frb_basic_ready_related :
    RdJobReadyRel Job jaR jaL costR costL PStateR PStateL R
      (@prosa.model.readiness.basic.basic_ready_instance Job PStateR jaR costR)
      (I.Prosa_Model_Readiness_Basic_basic_ready_instance Job dJ PStateL jaL costL).
  Proof.
    intros schedR schedL Hsched j tR tL Ht.
    exact (frb_pending_related schedR schedL Hsched j tR tL Ht).
  Qed.

  Definition src_basic_readiness_nonclairvoyance : Prop :=
    ltac:(body_of (fun s : S.statement_basic_readiness_nonclairvoyance => s Job PStateR jaR costR)).
  Definition tgt_basic_readiness_nonclairvoyance : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Readiness_Basic_basic_readiness_nonclairvoyance
      Job dJ PStateL jaL costL)).

  Theorem basic_readiness_nonclairvoyance_correspondence :
    PropSPropRel src_basic_readiness_nonclairvoyance tgt_basic_readiness_nonclairvoyance.
  Proof.
    exact (nonclairvoyant_readiness_correspondence Job jaR jaL costR costL PStateR PStateL R
      _ _ frb_basic_ready_related).
  Qed.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Definition src_basic_readiness_compliance : Prop :=
    ltac:(body_of (fun s : S.statement_basic_readiness_compliance => s Job PStateR jaR costR schedR)).
  Definition tgt_basic_readiness_compliance : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Readiness_Basic_basic_readiness_compliance
      Job dJ PStateL jaL costL schedL)).

  Theorem basic_readiness_compliance_correspondence :
    PropSPropRel src_basic_readiness_compliance tgt_basic_readiness_compliance.
  Proof.
    apply ar_imp_correspondence.
    { unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (frb_scheduled_at_related schedR schedL Hsched j tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)). }
    apply ar_imp_correspondence.
    { unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (frb_scheduled_at_related schedR schedL Hsched j tR tL Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _
        (rd_service_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht) (Hcost j)). }
    unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
    cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (frb_scheduled_at_related schedR schedL Hsched j tR tL Ht))|].
    exact (svc_bool_truth_correspondence _ _ (frb_basic_ready_related schedR schedL Hsched j tR tL Ht)).
  Qed.

  Lemma frb_exists_identity (P : Job -> Prop) (PL : Job -> SProp) :
    (forall j, PropSPropRel (P j) (PL j)) ->
    PropSPropRel (exists j, P j) (I.Exists Job PL).
  Proof.
    intro HP. apply prop_sprop_rel_intro.
    - intros [j Hj]. exact (I.Exists_intro Job PL j (prop_to_sprop _ _ (HP j) Hj)).
    - intros [j Hj]. apply strictly_inhabits. exists j. exact (sprop_to_prop _ _ (HP j) Hj).
  Qed.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Definition src_basic_readiness_is_work_bearing_readiness : Prop :=
    ltac:(body_of (fun s : S.statement_basic_readiness_is_work_bearing_readiness =>
      s Job PStateR jaR costR arrR schedR pR)).
  Definition tgt_basic_readiness_is_work_bearing_readiness : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Readiness_Basic_basic_readiness_is_work_bearing_readiness
      Job dJ PStateL jaL costL arrL schedL pL)).

  Theorem basic_readiness_is_work_bearing_readiness_correspondence :
    PropSPropRel src_basic_readiness_is_work_bearing_readiness
      tgt_basic_readiness_is_work_bearing_readiness.
  Proof.
    apply ar_imp_correspondence.
    { unfold prosa.model.priority.definitions.reflexive_job_priorities.
      cbn [I.Prosa_Model_Priority_Definitions_reflexive_job_priorities].
      apply ar_forall_identity_correspondence. intro j.
      exact (ar_bool_truth_correspondence _ _ (Hp j j)). }
    unfold prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
    cbn [I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (frb_pending_related schedR schedL Hsched j tR tL Ht))|].
    apply frb_exists_identity. intro j_hp.
    apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j_hp Harr)|].
    apply ar_and_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (frb_basic_ready_related schedR schedL Hsched j_hp tR tL Ht)).
    - exact (ar_bool_truth_correspondence _ _ (Hp j_hp j)).
  Qed.
End Basic.
