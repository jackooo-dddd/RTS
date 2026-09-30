(* Helper copy of the accepted OverheadResourceModelCorrespondence.v of the overhead-resource-model certificate chain, re-bound to this export; its
   arrivals-adapter imports are re-pointed to the replayed arrivals modules of this chain. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import OverheadResourceModelSemanticSource.
From prosa Require Import model.processor.overheads analysis.definitions.overheads.schedule_change.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaOvhFpFloatingNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations
  ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations
  ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence
  OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence.

Module I := ImportedRtaOvhFpFloatingNonpreemptive.
Module S := OverheadResourceModelSemanticSource.OverheadResourceModelSemanticSource.

(** Definition correspondences for [model/processor/overhead_resource_model.v].

    Source side: the extracted byte-identical definitions; target side: the compiled Lean definitions (the
    three [Finset.Ico] sums exported through their kernel-guarded list-interval projections).  Inputs: an
    overheads schedule pair related by the accepted pointwise state relation [OvhScheduleRel] of the accepted
    overheads processor-model certificate (hence also by the accepted schedule-change relation [ScScheduleRel]:
    both state maps are constructor-wise), option jobs by [ScOptionRel] (covered in both directions), instants
    and bounds by [SubNatRel].  [scheduled_job], [scheduled_job_invariant] and the [is_*] observations are the
    accepted certificates; interval sums the accepted interval-sum relation.  No source or target theorem is
    used. *)

Definition orm_opt_from {T : Type} (y : I.Option T) : option T :=
  match y with I.Option_some j => Some j | I.Option_none => None end.

Lemma orm_opt_from_rel {T : Type} (y : I.Option T) : ScOptionRel (orm_opt_from y) y.
Proof. destruct y; exact (@Lean.eq_refl _ _). Qed.

Lemma orm_forall_option (Job : eqType) (P : option Job -> Prop) (Q : I.Option Job -> SProp) :
  (forall oR oL, ScOptionRel oR oL -> PropSPropRel (P oR) (Q oL)) ->
  PropSPropRel (forall o, P o) (forall o, Q o).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR oL. exact (prop_to_sprop _ _ (H _ _ (orm_opt_from_rel oL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro oR.
    exact (sprop_to_prop _ _ (H _ _ (@Lean.eq_refl _ _)) (HL _)).
Qed.

Lemma orm_negb_related (b : bool) (bL : I.Bool) :
  ScBoolRel b bL -> ScBoolRel (~~ b) (I.Bool_not bL).
Proof.
  intro H. have E := imported_eq_to_coq_eq _ _ H. rewrite <- E. destruct b; exact (@Lean.eq_refl _ _).
Qed.

(** The boolean relations of the three adapters are the same map; truth is transported through the arrivals one. *)
Lemma orm_sc_ar (b : bool) (bL : I.Bool) : ScBoolRel b bL -> ArBoolRel b bL.
Proof. intro H. destruct b; exact H. Qed.

Lemma orm_ovh_ar (b : bool) (bL : I.Bool) : OvhBoolRel b bL -> ArBoolRel b bL.
Proof. intro H. destruct b; exact H. Qed.

Section Defs.
  Context (Job : eqType).
  Let dJ := ovh_decidable_eq Job.
  Let stateR : prosa.behavior.schedule.ProcessorState Job := @prosa.model.processor.overheads.processor_state Job.
  Variable schedR : prosa.behavior.schedule.schedule stateR.
  Variable schedL : Lean.Nat -> OvhTarget Job.
  Hypothesis Hsched : OvhScheduleRel Job schedR schedL.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Lemma orm_state_maps_agree (s : prosa.model.processor.overheads.proc_state Job) :
    Lean.eq (ovh_state_to_imported Job s) (sc_state_to_imported Job s).
  Proof.
    destruct s as [| a b | a | j | j]; cbn; try exact (@Lean.eq_refl _ _);
      try (destruct a, b; exact (@Lean.eq_refl _ _)); try (destruct a; exact (@Lean.eq_refl _ _)).
  Qed.

  Lemma orm_sc_sched : ScScheduleRel Job schedR schedL.
  Proof.
    intros tR tL Ht.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (orm_state_maps_agree (schedR tR))) (Hsched tR tL Ht)).
  Qed.

  Lemma orm_job_is_related tR tL oR oL :
    SubNatRel tR tL -> ScOptionRel oR oL ->
    ScBoolRel (@prosa.model.processor.overheads.scheduled_job Job schedR tR == oR)
      (I.Decidable_decide (Lean.eq (I.Prosa_Model_Processor_Overheads_scheduled_job Job dJ schedL tL) oL)
        (I.Option_instDecidableEq Job dJ (I.Prosa_Model_Processor_Overheads_scheduled_job Job dJ schedL tL) oL)).
  Proof.
    intros Ht Ho.
    exact (sc_option_eq_bool_correspondence Job _ _ _ _
      (sc_scheduled_job_correspondence Job schedR schedL tR tL orm_sc_sched Ht) Ho).
  Qed.

  Local Ltac spent obs := intros Ho H1 H2;
    apply svc_interval_sum_related; [exact H1|exact H2|];
    intros tR tL Ht; apply ovh_bool_to_nat_related;
    exact (sc_bool_and_related _ _ _ _ (orm_job_is_related _ _ _ _ Ht Ho)
      (obs Job schedR schedL tR tL Hsched Ht)).

  Lemma time_spent_in_dispatch_correspondence oR oL t1R t1L t2R t2L :
    ScOptionRel oR oL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@S.time_spent_in_dispatch Job schedR oR t1R t2R)
      (I.Prosa_Model_Processor_OverheadResourceModel_time_spent_in_dispatch Job dJ schedL oL t1L t2L).
  Proof. spent ovh_is_dispatch_correspondence. Qed.

  Lemma time_spent_in_context_switch_correspondence oR oL t1R t1L t2R t2L :
    ScOptionRel oR oL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@S.time_spent_in_context_switch Job schedR oR t1R t2R)
      (I.Prosa_Model_Processor_OverheadResourceModel_time_spent_in_context_switch Job dJ schedL oL t1L t2L).
  Proof. spent ovh_is_context_switch_correspondence. Qed.

  Lemma time_spent_in_CRPD_correspondence oR oL t1R t1L t2R t2L :
    ScOptionRel oR oL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@S.time_spent_in_CRPD Job schedR oR t1R t2R)
      (I.Prosa_Model_Processor_OverheadResourceModel_time_spent_in_CRPD Job dJ schedL oL t1L t2L).
  Proof. spent ovh_is_CRPD_correspondence. Qed.

  Local Ltac bounded spent_rel HB :=
    apply ar_forall_nat_correspondence; intros t1R t1L H1;
    apply ar_forall_nat_correspondence; intros t2R t2L H2;
    apply (orm_forall_option Job); intros oR oL Ho;
    imp (ar_bool_truth_correspondence _ _ (orm_sc_ar _ _
      (scheduled_job_invariant_correspondence Job schedR schedL orm_sc_sched _ _ _ _ _ _ Ho H1 H2)));
    exact (sub_nat_le_correspondence _ _ _ _ (spent_rel _ _ _ _ _ _ Ho H1 H2) HB).

  Lemma time_spent_in_dispatch_is_bounded_by_correspondence BR BL :
    SubNatRel BR BL ->
    PropSPropRel (@S.time_spent_in_dispatch_is_bounded_by Job schedR BR)
      (I.Prosa_Model_Processor_OverheadResourceModel_time_spent_in_dispatch_is_bounded_by Job dJ schedL BL).
  Proof. intro HB. bounded time_spent_in_dispatch_correspondence HB. Qed.

  Lemma time_spent_in_context_switch_is_bounded_by_correspondence BR BL :
    SubNatRel BR BL ->
    PropSPropRel (@S.time_spent_in_context_switch_is_bounded_by Job schedR BR)
      (I.Prosa_Model_Processor_OverheadResourceModel_time_spent_in_context_switch_is_bounded_by Job dJ schedL BL).
  Proof. intro HB. bounded time_spent_in_context_switch_correspondence HB. Qed.

  Lemma time_spent_in_CRPD_is_bounded_by_correspondence BR BL :
    SubNatRel BR BL ->
    PropSPropRel (@S.time_spent_in_CRPD_is_bounded_by Job schedR BR)
      (I.Prosa_Model_Processor_OverheadResourceModel_time_spent_in_CRPD_is_bounded_by Job dJ schedL BL).
  Proof. intro HB. bounded time_spent_in_CRPD_correspondence HB. Qed.

  Local Ltac precedes first later :=
    apply (orm_forall_option Job); intros oR oL Ho;
    apply ar_forall_nat_correspondence; intros t1R t1L H1;
    apply ar_forall_nat_correspondence; intros t2R t2L H2;
    imp (ar_bool_truth_correspondence _ _ (orm_sc_ar _ _
      (scheduled_job_invariant_correspondence Job schedR schedL orm_sc_sched _ _ _ _ _ _ Ho H1 H2)));
    apply ar_forall_nat_correspondence; intros tR tL Ht;
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ H1 Ht) (ar_decide_lt_related _ _ _ _ Ht H2)));
    imp (ar_bool_truth_correspondence _ _ (orm_ovh_ar _ _ (first Job schedR schedL tR tL Hsched Ht)));
    apply ar_forall_nat_correspondence; intros uR uL Hu;
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ H1 Hu) (ar_decide_le_related _ _ _ _ Hu Ht)));
    exact (ar_bool_truth_correspondence _ _ (orm_sc_ar _ _ (orm_negb_related _ _ (later Job schedR schedL uR uL Hsched Hu)))).

  Lemma dispatch_precedes_context_switch_correspondence :
    PropSPropRel (@S.dispatch_precedes_context_switch Job schedR)
      (I.Prosa_Model_Processor_OverheadResourceModel_dispatch_precedes_context_switch Job dJ schedL).
  Proof. precedes ovh_is_dispatch_correspondence ovh_is_context_switch_correspondence. Qed.

  Lemma context_switch_precedes_progress_correspondence :
    PropSPropRel (@S.context_switch_precedes_progress Job schedR)
      (I.Prosa_Model_Processor_OverheadResourceModel_context_switch_precedes_progress Job dJ schedL).
  Proof. precedes ovh_is_context_switch_correspondence ovh_is_progress_correspondence. Qed.

  Lemma context_switch_precedes_CRPD_correspondence :
    PropSPropRel (@S.context_switch_precedes_CRPD Job schedR)
      (I.Prosa_Model_Processor_OverheadResourceModel_context_switch_precedes_CRPD Job dJ schedL).
  Proof. precedes ovh_is_context_switch_correspondence ovh_is_CRPD_correspondence. Qed.

  Lemma overhead_resource_model_correspondence DR DL CR CL PR PL :
    SubNatRel DR DL -> SubNatRel CR CL -> SubNatRel PR PL ->
    PropSPropRel (@S.overhead_resource_model Job schedR DR CR PR)
      (I.Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model Job dJ schedL DL CL PL).
  Proof.
    intros HD HC HP. unfold S.overhead_resource_model.
    cbn [I.Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model].
    apply ar_and_correspondence; [exact (time_spent_in_dispatch_is_bounded_by_correspondence _ _ HD)|].
    apply ar_and_correspondence; [exact (time_spent_in_context_switch_is_bounded_by_correspondence _ _ HC)|].
    apply ar_and_correspondence; [exact (time_spent_in_CRPD_is_bounded_by_correspondence _ _ HP)|].
    apply ar_and_correspondence; [exact dispatch_precedes_context_switch_correspondence|].
    apply ar_and_correspondence; [exact context_switch_precedes_progress_correspondence|].
    exact context_switch_precedes_CRPD_correspondence.
  Qed.
End Defs.
