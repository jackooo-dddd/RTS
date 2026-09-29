From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import PriorityBumpFactsSemanticSource.
From prosa Require Import behavior.all model.processor.overheads model.readiness.basic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheadsPriorityBumpFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence
  OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers
  OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers
  OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel PriorityBumpCorrespondence.

Module I := ImportedOverheadsPriorityBumpFacts.
Module S := PriorityBumpFactsSemanticSource.PriorityBumpFactsSemanticSource.

(** Statement correspondences for [analysis/facts/model/overheads/priority_bump.v].

    Source side: the extracted statements specialised at the job type; target side: the imported Lean theorem
    types.  The overheads processor model is fixed on both sides and related by [ovh_psrel] (OvhStateRel.v, as in
    the accepted overheads-schedule certificate); the generic chain helpers are replayed at its universe instance
    (Ovh*.v, see their headers).  Job-arrival and job-cost instances, JLFP policies, arrival sequences, schedules
    and preemption models are covered in both directions; the basic readiness model (fixed on both sides) is
    related pointwise at the statement's schedule pair through [pending]; jobs by identity, instants by
    [SubNatRel].  [priority_bump] is the accepted definition certificate, re-bound to this export and reached
    through two bridges: its schedule relation agrees with [ovh_psrel] constructor-wise, and its Boolean
    relation is the arrivals one.  No source or target theorem is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

Lemma pbf_pb_ar (b : bool) (bL : I.Bool) : PbBoolRel b bL -> ArBoolRel b bL.
Proof. intro H. destruct b; exact H. Qed.

Lemma pbf_ar_pb (b : bool) (bL : I.Bool) : ArBoolRel b bL -> PbBoolRel b bL.
Proof. intro H. destruct b; exact H. Qed.

Section Stmts.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.overheads.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Overheads_processor_state Job dJ.
  Let X := ovh_psrel Job.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Lemma pbf_sched_rel sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) : PbScheduleRel Job sR sL.
  Proof.
    intros tR tL Ht.
    refine (sub_imported_eq_trans _ _ _ _ (Hs tR tL Ht)). cbn.
    destruct (sR tR) as [| a b | a | j | j]; cbn; try destruct a; try destruct b; exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pbf_jlfp_rel pR pL (Hp : FpreJLFPRel Job pR pL) : PbJLFPRel Job pR pL.
  Proof. intros x y. exact (pbf_ar_pb _ _ (Hp x y)). Qed.

  Lemma pbf_bump_related pR pL (Hp : FpreJLFPRel Job pR pL) sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) tR tL :
    SubNatRel tR tL ->
    ArBoolRel (@prosa.analysis.definitions.overheads.priority_bump.priority_bump Job pR sR tR)
      (I.Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump Job dJ pL sL tL).
  Proof.
    intro Ht.
    exact (pbf_pb_ar _ _ (priority_bump_correspondence Job pR pL (pbf_jlfp_rel pR pL Hp) sR sL tR tL
      (pbf_sched_rel sR sL Hs) Ht)).
  Qed.

  Lemma pbf_not_bump_related pR pL (Hp : FpreJLFPRel Job pR pL) sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) tR tL :
    SubNatRel tR tL ->
    ArBoolRel (~~ @prosa.analysis.definitions.overheads.priority_bump.priority_bump Job pR sR tR)
      (I.Bool_not (I.Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump Job dJ pL sL tL)).
  Proof.
    intro Ht.
    exact (pbf_pb_ar _ _ (pb_bool_not_related _ _ (pbf_ar_pb _ _ (pbf_bump_related pR pL Hp sR sL Hs tR tL Ht)))).
  Qed.

  Lemma pbf_forall_ja (P : prosa.behavior.job.JobArrival Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobArrival Job dJ -> SProp) :
    (forall a b, ArJobArrivalRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (ArJobArrivalRel Job) (ar_import_job_arrival Job)
      (svc_export_job_arrival Job) (ar_job_arrival_import_certificate Job) (svc_job_arrival_export Job) P Q).
  Qed.

  Lemma pbf_forall_cost (P : prosa.behavior.job.JobCost Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobCost Job dJ -> SProp) :
    (forall a b, SvcJobCostRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (SvcJobCostRel Job) (svc_import_job_cost Job)
      (svc_export_job_cost Job) (svc_job_cost_import Job) (svc_job_cost_export Job) P Q).
  Qed.

  Section Basic.
    Variable jaR : prosa.behavior.job.JobArrival Job.
    Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
    Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
    Variable costR : prosa.behavior.job.JobCost Job.
    Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
    Hypothesis Hcost : SvcJobCostRel Job costR costL.

    Lemma pbf_basic_ready_rel sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) :
      FpreJrAt Job jaR jaL costR costL PR PL sR sL
        (@prosa.model.readiness.basic.basic_ready_instance Job PR jaR costR)
        (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PL jaL costL).
    Proof.
      intros j tR tL Ht.
      exact (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht).
    Qed.
  End Basic.

  Ltac pbf_prefix jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs :=
    apply pbf_forall_ja; intros jaR jaL Hja;
    apply pbf_forall_cost; intros costR costL Hcost;
    apply (fpre_forall_jlfp Job); intros pR pL Hp;
    imp (fpre_reflexive_rel Job pR pL Hp).
  Ltac pbf_sched jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs :=
    apply (fpre_forall_arr Job); intros arrR arrL Harr;
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr);
    apply (fpre_forall_sched Job PR PL X); intros sR sL Hs;
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (pbf_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs)).

  Definition src_priority_bump_implies_preemption_time : Prop :=
    ltac:(body_of (fun s : S.statement_priority_bump_implies_preemption_time => s Job)).
  Definition tgt_priority_bump_implies_preemption_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_PriorityBump_priority_bump_implies_preemption_time Job dJ)).
  Theorem priority_bump_implies_preemption_time_correspondence :
    PropSPropRel src_priority_bump_implies_preemption_time tgt_priority_bump_implies_preemption_time.
  Proof.
    unfold src_priority_bump_implies_preemption_time, tgt_priority_bump_implies_preemption_time.
    pbf_prefix jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs.
    pbf_sched jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs.
    apply (fpre_forall_jp Job); intros jpR jpL Hjp.
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (pbf_bump_related pR pL Hp sR sL Hs tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _
      (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp tR tL Ht)).
  Qed.

  Ltac pbf_common jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs jpR jpL Hjp j t1R t1L Ht1 t2R t2L Ht2 :=
    pbf_prefix jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs;
    imp (hap_transitive_rel Job pR pL Hp);
    pbf_sched jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs;
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (pbf_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs));
    apply (fpre_forall_jp Job); intros jpR jpL Hjp;
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp);
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (pbf_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs) jpR jpL Hjp pR pL Hp);
    apply ar_forall_identity_correspondence; intro j;
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr);
    imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j));
    apply ar_forall_nat_correspondence; intros t1R t1L Ht1;
    apply ar_forall_nat_correspondence; intros t2R t2L Ht2;
    imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
      pR pL Hp j t1R t1L t2R t2L Ht1 Ht2).

  Definition src_priority_bump_implies_hp_arrival_in_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_priority_bump_implies_hp_arrival_in_prefix => s Job)).
  Definition tgt_priority_bump_implies_hp_arrival_in_prefix : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_PriorityBump_priority_bump_implies_hp_arrival_in_prefix Job dJ)).
  Theorem priority_bump_implies_hp_arrival_in_prefix_correspondence :
    PropSPropRel src_priority_bump_implies_hp_arrival_in_prefix tgt_priority_bump_implies_hp_arrival_in_prefix.
  Proof.
    unfold src_priority_bump_implies_hp_arrival_in_prefix, tgt_priority_bump_implies_hp_arrival_in_prefix.
    pbf_common jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs jpR jpL Hjp j t1R t1L Ht1 t2R t2L Ht2.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros taR taL Hta.
    imp (sub_nat_le_correspondence _ _ _ _ Ht1 Ht).
    imp (sub_nat_lt_correspondence _ _ _ _ Ht Hta).
    imp (sub_nat_le_correspondence _ _ _ _ Hta Ht2).
    imp (ar_bool_truth_correspondence _ _ (pbf_bump_related pR pL Hp sR sL Hs tR tL Ht)).
    apply ex_exists_identity. intro jhp.
    apply ar_and_correspondence.
    - exact (ar_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs jhp _ _ Ht)).
    - exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job jhp _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1 Hta))).
  Qed.

  Definition src_no_priority_bumps_in_fifo : Prop :=
    ltac:(body_of (fun s : S.statement_no_priority_bumps_in_fifo => s Job)).
  Definition tgt_no_priority_bumps_in_fifo : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_PriorityBump_no_priority_bumps_in_fifo Job dJ)).
  Theorem no_priority_bumps_in_fifo_correspondence :
    PropSPropRel src_no_priority_bumps_in_fifo tgt_no_priority_bumps_in_fifo.
  Proof.
    unfold src_no_priority_bumps_in_fifo, tgt_no_priority_bumps_in_fifo.
    pbf_common jaR jaL Hja costR costL Hcost pR pL Hp arrR arrL Harr sR sL Hs jpR jpL Hjp j t1R t1L Ht1 t2R t2L Ht2.
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      exact (ar_bool_eq_correspondence _ _ _ _ (Hp j1 j2) (ar_decide_le_related _ _ _ _ (Hja j1) (Hja j2))). }
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_lt_related _ _ _ _ Ht1 Ht) (ar_decide_le_related _ _ _ _ Ht Ht2))).
    exact (ar_bool_truth_correspondence _ _ (pbf_not_bump_related pR pL Hp sR sL Hs tR tL Ht)).
  Qed.
End Stmts.
