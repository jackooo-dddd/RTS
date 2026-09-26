From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsBackloggedSemanticSource.
From prosa Require Import model.schedule.work_conserving analysis.definitions.schedule_prefix.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsBacklogged ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence
  ReadinessCorrespondence.

Module I := ImportedFactsBacklogged.
Module S := FactsBackloggedSemanticSource.FactsBackloggedSemanticSource.

(** Statement correspondences for [analysis/facts/readiness/backlogged.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: [job_arrival] by [ArJobArrivalRel], [job_cost] by
    [SvcJobCostRel], processor states by the accepted two-sided
    [SvcProcessorStateRel], the readiness model by the accepted
    [RdJobReadyRel], schedules and arrival sequences by the accepted relations
    (covered in both directions through the accepted readiness and arrival
    covers where they are quantified inside a statement).  [backlogged] and
    [jobs_backlogged_at] are related through the accepted filter and
    [arrivals_up_to] certificates, [identical_prefix] and
    [nonclairvoyant_readiness] through the accepted readiness certificate.
    No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Definition fbl_arrival_sequence_to_source (Job : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
    prosa.behavior.arrival_sequence.arrival_sequence Job :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma fbl_arrival_sequence_to_source_rel (Job : eqType) arrL :
  ArArrivalSequenceRel Job (fbl_arrival_sequence_to_source Job arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, fbl_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

Section Backlogged.
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
  Variable readyR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
  Variable readyL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL.
  Hypothesis Hready : RdJobReadyRel Job jaR jaL costR costL PStateR PStateL R readyR readyL.

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Lemma fbl_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at].
      exact (svc_scheduled_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma fbl_backlogged_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArBoolRel (@prosa.behavior.ready.backlogged Job PStateR costR jaR readyR schedR j tR)
        (I.Prosa_Behavior_Ready_backlogged Job dJ PStateL costL jaL readyL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.ready.backlogged.
      cbn [I.Prosa_Behavior_Ready_backlogged].
      apply ar_bool_and_related.
      - exact (Hready schedR schedL Hsched j tR tL Ht).
      - exact (svc_bool_not_related _ _ (fbl_scheduled_at_related j tR tL Ht)).
    Qed.

    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Lemma fbl_jobs_backlogged_at_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArListRel (@prosa.model.schedule.work_conserving.jobs_backlogged_at Job jaR costR PStateR readyR arrR schedR tR)
        (I.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at Job dJ jaL costL PStateL readyL arrL schedL tL).
    Proof.
      intro Ht. unfold prosa.model.schedule.work_conserving.jobs_backlogged_at.
      cbn [I.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at].
      apply ar_filter_related.
      - intro j. exact (fbl_backlogged_related j tR tL Ht).
      - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
    Qed.

    Definition src_mem_backlogged_jobs : Prop :=
      ltac:(body_of (fun s : S.statement_mem_backlogged_jobs => s Job costR jaR PStateR readyR arrR schedR)).
    Definition tgt_mem_backlogged_jobs : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Readiness_Backlogged_mem_backlogged_jobs
        Job dJ costL jaL PStateL readyL arrL schedL)).

    Theorem mem_backlogged_jobs_correspondence :
      PropSPropRel src_mem_backlogged_jobs tgt_mem_backlogged_jobs.
    Proof.
      apply ar_imp_correspondence;
        [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (fbl_backlogged_related j tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _
        (ar_decide_mem_related Job j _ _ (fbl_jobs_backlogged_at_related tR tL Ht))).
    Qed.

    Definition src_backlogged_job_arrives_in : Prop :=
      ltac:(body_of (fun s : S.statement_backlogged_job_arrives_in => s Job costR jaR PStateR readyR arrR schedR)).
    Definition tgt_backlogged_job_arrives_in : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Readiness_Backlogged_backlogged_job_arrives_in
        Job dJ costL jaL PStateL readyL arrL schedL)).

    Theorem backlogged_job_arrives_in_correspondence :
      PropSPropRel src_backlogged_job_arrives_in tgt_backlogged_job_arrives_in.
    Proof.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (ar_decide_mem_related Job j _ _ (fbl_jobs_backlogged_at_related tR tL Ht)))|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.
  End Sched.

  (** *** Prefix invariance (schedules covered through the accepted readiness covers) *)

  Let NONCLAIR := nonclairvoyant_readiness_correspondence Job jaR jaL costR costL PStateR PStateL R readyR readyL Hready.

  Lemma fbl_forall_schedule
      (PR : @prosa.behavior.schedule.schedule Job PStateR -> Prop)
      (PL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL -> SProp) :
    (forall schedR schedL, RdScheduleFunRel Job PStateR PStateL R schedR schedL ->
      PropSPropRel (PR schedR) (PL schedL)) ->
    PropSPropRel (forall schedR, PR schedR) (forall schedL, PL schedL).
  Proof.
    exact (rd_forall_cover_sprop _ _ (RdScheduleFunRel Job PStateR PStateL R)
      (rd_schedule_to_target Job PStateR PStateL R) (rd_schedule_to_source Job PStateR PStateL R)
      (rd_schedule_to_target_rel Job PStateR PStateL R) (rd_schedule_to_source_rel Job PStateR PStateL R) PR PL).
  Qed.

  Let SVC schedR schedL (Hf : RdScheduleFunRel Job PStateR PStateL R schedR schedL) :=
    rd_schedule_fun_to_svc Job PStateR PStateL R schedR schedL Hf.

  Definition src_backlogged_prefix_invariance : Prop :=
    ltac:(body_of (fun s : S.statement_backlogged_prefix_invariance => s Job costR jaR PStateR readyR)).
  Definition tgt_backlogged_prefix_invariance : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Readiness_Backlogged_backlogged_prefix_invariance
      Job dJ costL jaL PStateL readyL)).

  Theorem backlogged_prefix_invariance_correspondence :
    PropSPropRel src_backlogged_prefix_invariance tgt_backlogged_prefix_invariance.
  Proof.
    apply ar_imp_correspondence; [exact NONCLAIR|].
    apply fbl_forall_schedule. intros schedR schedL Hf.
    apply fbl_forall_schedule. intros schedR' schedL' Hf'.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence;
      [exact (rd_identical_prefix_correspondence Job PStateR PStateL R _ _ _ _ Hf Hf' hR hL Hh)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh)|].
    exact (rd_bool_eq_correspondence _ _ _ _
      (fbl_backlogged_related schedR schedL (SVC _ _ Hf) j tR tL Ht)
      (fbl_backlogged_related schedR' schedL' (SVC _ _ Hf') j tR tL Ht)).
  Qed.

  Definition src_backlogged_prefix_invariance' : Prop :=
    ltac:(body_of (fun s : S.statement_backlogged_prefix_invariance' => s Job costR jaR PStateR readyR)).
  Definition tgt_backlogged_prefix_invariance' : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Readiness_Backlogged_backlogged_prefix_invariance'
      Job dJ costL jaL PStateL readyL)).

  Theorem backlogged_prefix_invariance'_correspondence :
    PropSPropRel src_backlogged_prefix_invariance' tgt_backlogged_prefix_invariance'.
  Proof.
    apply ar_imp_correspondence; [exact NONCLAIR|].
    apply fbl_forall_schedule. intros schedR schedL Hf.
    apply fbl_forall_schedule. intros schedR' schedL' Hf'.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence;
      [exact (rd_identical_prefix_correspondence Job PStateR PStateL R _ _ _ _ Hf Hf' hR hL Hh)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _
        (svc_bool_not_related _ _ (fbl_scheduled_at_related schedR schedL (SVC _ _ Hf) j tR tL Ht)))|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _
        (svc_bool_not_related _ _ (fbl_scheduled_at_related schedR' schedL' (SVC _ _ Hf') j tR tL Ht)))|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hh)|].
    exact (rd_bool_eq_correspondence _ _ _ _
      (fbl_backlogged_related schedR schedL (SVC _ _ Hf) j tR tL Ht)
      (fbl_backlogged_related schedR' schedL' (SVC _ _ Hf') j tR tL Ht)).
  Qed.

  Definition src_backlogged_jobs_prefix_invariance : Prop :=
    ltac:(body_of (fun s : S.statement_backlogged_jobs_prefix_invariance => s Job costR jaR PStateR readyR)).
  Definition tgt_backlogged_jobs_prefix_invariance : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Readiness_Backlogged_backlogged_jobs_prefix_invariance
      Job dJ costL jaL PStateL readyL)).

  Theorem backlogged_jobs_prefix_invariance_correspondence :
    PropSPropRel src_backlogged_jobs_prefix_invariance tgt_backlogged_jobs_prefix_invariance.
  Proof.
    apply ar_imp_correspondence; [exact NONCLAIR|].
    apply (rd_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
      (ar_arrival_sequence_to_imported Job) (fbl_arrival_sequence_to_source Job)
      (ar_arrival_sequence_canonical Job) (fbl_arrival_sequence_to_source_rel Job)).
    intros arrR arrL Harr.
    apply fbl_forall_schedule. intros schedR schedL Hf.
    apply fbl_forall_schedule. intros schedR' schedL' Hf'.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence;
      [exact (rd_identical_prefix_correspondence Job PStateR PStateL R _ _ _ _ Hf Hf' hR hL Hh)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh)|].
    exact (ar_list_eq_correspondence Job _ _ _ _
      (fbl_jobs_backlogged_at_related schedR schedL (SVC _ _ Hf) arrR arrL Harr tR tL Ht)
      (fbl_jobs_backlogged_at_related schedR' schedL' (SVC _ _ Hf') arrR arrL Harr tR tL Ht)).
  Qed.
End Backlogged.
