From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import OverheadsScheduleSemanticSource.
From prosa Require Import behavior.all model.processor.overheads model.processor.platform_properties model.processor.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheadsSchedule ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence
  OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers
  OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhStateRel.

Module I := ImportedOverheadsSchedule.
Module S := OverheadsScheduleSemanticSource.OverheadsScheduleSemanticSource.

(** Statement correspondences for [analysis/facts/model/overheads/schedule.v].

    Source side: the extracted statements specialised at the job type; target side: the imported Lean theorem
    types.  The overheads processor model is fixed on both sides and related by [ovh_psrel] (OvhStateRel.v: a
    constructor-wise state bijection with both roundtrips, the unit core, [scheduled_on] per core, and
    [service_in]/[supply_in] through the kernel-checked interface equations).  Its statements use universe-
    specialised copies of the processor-model constants; the generic chain helpers are replayed at that instance
    (Ovh*.v, see their headers), made available by the validation-only witness fixture.  Schedules, JLFP
    policies, arrival sequences, job-arrival and job-cost instances and the readiness model at the statement's
    schedule pair are covered in both directions; jobs by identity, instants by [SubNatRel].  No source or target
    theorem is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

Section Stmts.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.overheads.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Overheads_processor_state Job dJ.
  Let X := ovh_psrel Job.

  Definition src_overheads_proc_model_is_a_uniprocessor_model : Prop :=
    ltac:(body_of (fun s : S.statement_overheads_proc_model_is_a_uniprocessor_model => s Job)).
  Definition tgt_overheads_proc_model_is_a_uniprocessor_model : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Schedule_overheads_proc_model_is_a_uniprocessor_model Job dJ)).
  Theorem overheads_proc_model_is_a_uniprocessor_model_correspondence :
    PropSPropRel src_overheads_proc_model_is_a_uniprocessor_model
      tgt_overheads_proc_model_is_a_uniprocessor_model.
  Proof. exact (isj_psr_uniprocessor_related Job PR PL X). Qed.

  Definition src_overheads_proc_model_provides_unit_supply : Prop :=
    ltac:(body_of (fun s : S.statement_overheads_proc_model_provides_unit_supply => s Job)).
  Definition tgt_overheads_proc_model_provides_unit_supply : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Schedule_overheads_proc_model_provides_unit_supply Job dJ)).
  Theorem overheads_proc_model_provides_unit_supply_correspondence :
    PropSPropRel src_overheads_proc_model_provides_unit_supply
      tgt_overheads_proc_model_provides_unit_supply.
  Proof.
    unfold src_overheads_proc_model_provides_unit_supply, tgt_overheads_proc_model_provides_unit_supply.
    unfold prosa.model.processor.platform_properties.unit_supply_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4].
    apply (isj_forall_cover_sprop _ _
      (fun sR sL => Lean.eq (isj_st_to Job PR PL X sR) sL) (isj_st_to Job PR PL X)
      (isj_st_from Job PR PL X) (fun _ => @Lean.eq_refl _ _) (isj_st_rt_target Job PR PL X)).
    intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (isj_lean_transport
      (fun sL => SubNatRel (@prosa.behavior.schedule.supply_in Job PR sR)
         (I.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4 Job dJ PL sL))
      _ _ Hs (isj_sup_in_rel Job PR PL X sR)) (sub_nat_rel_canonical 1)).
  Qed.

  Lemma ovh_supply_at_related sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) tR tL :
    SubNatRel tR tL ->
    SubNatRel (@prosa.model.processor.supply.supply_at Job PR sR tR)
      (I.Prosa_Model_Processor_Supply_supply_at_inst4 Job dJ PL sL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.supply_at.
    cbn [I.Prosa_Model_Processor_Supply_supply_at_inst4].
    exact (isj_lean_transport
      (fun s => SubNatRel (@prosa.behavior.schedule.supply_in Job PR (sR tR))
         (I.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4 Job dJ PL s))
      _ _ (Hs tR tL Ht) (isj_sup_in_rel Job PR PL X (sR tR))).
  Qed.

  Definition src_overheads_proc_model_fully_consuming : Prop :=
    ltac:(body_of (fun s : S.statement_overheads_proc_model_fully_consuming => s Job)).
  Definition tgt_overheads_proc_model_fully_consuming : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Schedule_overheads_proc_model_fully_consuming Job dJ)).
  Theorem overheads_proc_model_fully_consuming_correspondence :
    PropSPropRel src_overheads_proc_model_fully_consuming tgt_overheads_proc_model_fully_consuming.
  Proof.
    unfold src_overheads_proc_model_fully_consuming, tgt_overheads_proc_model_fully_consuming.
    unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (isj_psr_service_at_related Job PR PL X sR sL Hs j _ _ Ht)
      (ovh_supply_at_related sR sL Hs _ _ Ht)).
  Qed.

  Lemma ovh_opt_eq_correspondence (oR cR : option Job) (oL cL : I.Option Job) :
    Lean.eq (ovh_opt_to Job oR) oL -> Lean.eq (ovh_opt_to Job cR) cL ->
    PropSPropRel (oR = cR) (Lean.eq oL cL).
  Proof.
    intros Ho Hc. apply prop_sprop_rel_intro.
    - intro E. destruct E. exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ho) Hc).
    - intro E. apply strictly_inhabits.
      have EL := imported_eq_to_coq_eq _ _
        (sub_imported_eq_trans _ _ _ Ho (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
      rewrite -(ovh_opt_rt_source Job oR) -(ovh_opt_rt_source Job cR) EL. reflexivity.
  Qed.

  Lemma ovh_scheduled_job_related sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) tR tL :
    SubNatRel tR tL ->
    Lean.eq (ovh_opt_to Job (prosa.model.processor.overheads.scheduled_job sR tR))
      (I.Prosa_Model_Processor_Overheads_scheduled_job Job dJ sL tL).
  Proof.
    intro Ht. have E := Hs tR tL Ht.
    unfold prosa.model.processor.overheads.scheduled_job.
    unfold I.Prosa_Model_Processor_Overheads_scheduled_job.
    revert E. generalize (sL tL). intros sl E. destruct E.
    destruct (sR tR) as [| a b | a | j | j]; cbn; try exact (@Lean.eq_refl _ _);
      try (destruct b; exact (@Lean.eq_refl _ _)); try (destruct a; exact (@Lean.eq_refl _ _)).
  Qed.

  Definition src_scheduled_job_dec : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_job_dec => s Job)).
  Definition tgt_scheduled_job_dec : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Schedule_scheduled_job_dec Job dJ)).
  Theorem scheduled_job_dec_correspondence :
    PropSPropRel src_scheduled_job_dec tgt_scheduled_job_dec.
  Proof.
    unfold src_scheduled_job_dec, tgt_scheduled_job_dec.
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    have Hj := ovh_scheduled_job_related sR sL Hs tR tL Ht.
    apply fpre_or_correspondence.
    - exact (ovh_opt_eq_correspondence _ None _ _ Hj (@Lean.eq_refl _ _)).
    - apply ex_exists_identity. intro j.
      exact (ovh_opt_eq_correspondence _ (Some j) _ _ Hj (@Lean.eq_refl _ _)).
  Qed.

  Definition src_scheduled_at_iff_scheduled_job : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_at_iff_scheduled_job => s Job)).
  Definition tgt_scheduled_at_iff_scheduled_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Schedule_scheduled_at_iff_scheduled_job Job dJ)).
  Theorem scheduled_at_iff_scheduled_job_correspondence :
    PropSPropRel src_scheduled_at_iff_scheduled_job tgt_scheduled_at_iff_scheduled_job.
  Proof.
    unfold src_scheduled_at_iff_scheduled_job, tgt_scheduled_at_iff_scheduled_job.
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply pp_iff_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht)).
    - exact (ovh_opt_eq_correspondence _ (Some j) _ _ (ovh_scheduled_job_related sR sL Hs tR tL Ht)
        (@Lean.eq_refl _ _)).
  Qed.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Lemma ovh_forall_ja (P : prosa.behavior.job.JobArrival Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobArrival Job dJ -> SProp) :
    (forall a b, ArJobArrivalRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (ArJobArrivalRel Job) (ar_import_job_arrival Job)
      (svc_export_job_arrival Job) (ar_job_arrival_import_certificate Job) (svc_job_arrival_export Job) P Q).
  Qed.

  Lemma ovh_forall_cost (P : prosa.behavior.job.JobCost Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobCost Job dJ -> SProp) :
    (forall a b, SvcJobCostRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (SvcJobCostRel Job) (svc_import_job_cost Job)
      (svc_export_job_cost Job) (svc_job_cost_import Job) (svc_job_cost_export Job) P Q).
  Qed.

  Definition src_job_scheduled_in_busy_interval_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_job_scheduled_in_busy_interval_prefix => s Job)).
  Definition tgt_job_scheduled_in_busy_interval_prefix : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Schedule_job_scheduled_in_busy_interval_prefix Job dJ)).
  Theorem job_scheduled_in_busy_interval_prefix_correspondence :
    PropSPropRel src_job_scheduled_in_busy_interval_prefix tgt_job_scheduled_in_busy_interval_prefix.
  Proof.
    unfold src_job_scheduled_in_busy_interval_prefix, tgt_job_scheduled_in_busy_interval_prefix.
    apply ovh_forall_ja. intros jaR jaL Hja.
    apply ovh_forall_cost. intros costR costL Hcost.
    apply (fpre_forall_jlfp Job). intros pR pL Hp.
    imp (fpre_reflexive_rel Job pR pL Hp).
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs). intros jrR jrL Hjr.
    imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
      pR pL Hp jrR jrL Hjr).
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
      pR pL Hp j t1R t1L t2R t2L Ht1 Ht2).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
         (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2)))|].
    apply ex_exists_identity. intro jo.
    exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs jo _ _ Ht)).
  Qed.
End Stmts.
