From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import ScheduleChangeFactsSemanticSource.
From prosa Require Import behavior.all model.processor.overheads analysis.definitions.overheads.schedule_change.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheadsScheduleChangeFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPStateCoverHelpers OvhFactsPreemptionHelpers
  OvhStateRel
  ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations
  ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence.

Module I := ImportedOverheadsScheduleChangeFacts.
Module S := ScheduleChangeFactsSemanticSource.ScheduleChangeFactsSemanticSource.

(** Statement correspondences for [analysis/facts/model/overheads/schedule_change.v].

    Source side: the extracted statements specialised at the job type; target side: the imported Lean
    theorem types.  The overheads processor model is fixed on both sides; schedules are covered in both
    directions through the accepted concrete processor relation [ovh_psrel] (as in the accepted
    overheads-schedule certificate), and each related schedule pair is also related by the accepted
    schedule-change definitions relation [ScScheduleRel] (both state maps are constructor-wise, so they agree
    pointwise).  [schedule_change], [number_schedule_changes], [no_schedule_changes_during],
    [scheduled_job_invariant] and [scheduled_job] are the accepted schedule-change definition certificates,
    re-bound to this export.  Instants and counts by [SubNatRel]; option jobs by [ScOptionRel], covered in
    both directions.  No source or target theorem is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

Section Stmts.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.overheads.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Overheads_processor_state Job dJ.
  Let X := ovh_psrel Job.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  (** The two state maps agree, so a schedule pair related through [ovh_psrel] is related by [ScScheduleRel]. *)
  Lemma ovhsc_state_maps_agree (s : prosa.model.processor.overheads.proc_state Job) :
    Lean.eq (ovh_st_to Job s) (sc_state_to_imported Job s).
  Proof.
    destruct s as [| a b | a | j | j]; cbn; try exact (@Lean.eq_refl _ _);
      try (destruct a, b; exact (@Lean.eq_refl _ _)); try (destruct a; exact (@Lean.eq_refl _ _)).
  Qed.

  Lemma ovhsc_sched_rel sR sL :
    IsjPSchedRel Job PR PL X sR sL -> ScScheduleRel Job sR sL.
  Proof.
    intros Hs tR tL Ht.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (ovhsc_state_maps_agree (sR tR))) (Hs tR tL Ht)).
  Qed.

  Lemma ovhsc_forall_option (P : option Job -> Prop) (Q : I.Option Job -> SProp) :
    (forall oR oL, ScOptionRel oR oL -> PropSPropRel (P oR) (Q oL)) ->
    PropSPropRel (forall o, P o) (forall o, Q o).
  Proof.
    exact (isj_forall_cover_sprop _ _ ScOptionRel sc_option_to_imported (ovh_opt_from Job)
      (fun _ => @Lean.eq_refl _ _)
      (fun y => match y as y0 return ScOptionRel (ovh_opt_from Job y0) y0 with
                | I.Option_some j => @Lean.eq_refl _ _
                | I.Option_none => @Lean.eq_refl _ _ end) P Q).
  Qed.

  Local Ltac cover_sched := apply (fpre_forall_sched Job PR PL X); intros sR sL Hs;
    have Hsc := ovhsc_sched_rel sR sL Hs.

  Definition src_number_schedule_changes_cat : Prop :=
    ltac:(body_of (fun s : S.statement_number_schedule_changes_cat => s Job)).
  Definition tgt_number_schedule_changes_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_number_schedule_changes_cat Job dJ)).
  Theorem number_schedule_changes_cat_correspondence :
    PropSPropRel src_number_schedule_changes_cat tgt_number_schedule_changes_cat.
  Proof.
    unfold src_number_schedule_changes_cat, tgt_number_schedule_changes_cat.
    cover_sched.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
         (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_le_related _ _ _ _ Ht Ht2)))|].
    exact (sub_nat_eq_correspondence _ _ _ _
      (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Ht1 Ht2)
      (svc_target_add_related _ _ _ _
        (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Ht1 Ht)
        (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Ht Ht2))).
  Qed.

  Definition src_first_schedule_change_exists : Prop :=
    ltac:(body_of (fun s : S.statement_first_schedule_change_exists => s Job)).
  Definition tgt_first_schedule_change_exists : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_first_schedule_change_exists Job dJ)).
  Theorem first_schedule_change_exists_correspondence :
    PropSPropRel src_first_schedule_change_exists tgt_first_schedule_change_exists.
  Proof.
    unfold src_first_schedule_change_exists, tgt_first_schedule_change_exists.
    cover_sched.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_nat_correspondence. intros kR kL Hk.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hk).
    imp (sub_nat_eq_correspondence _ _ _ _ (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Ht1 Ht2) Hk).
    apply ar_exists_nat_correspondence. intros tR tL Ht.
    apply ar_and_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
         (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2)))|].
    apply ar_and_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (schedule_change_correspondence Job sR sL Hsc _ _ Ht))|].
    apply ar_and_correspondence.
    - exact (sub_nat_eq_correspondence _ _ _ _ (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Ht1 Ht)
        (sub_nat_rel_canonical 0)).
    - exact (sub_nat_eq_correspondence _ _ _ _ (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Ht Ht2) Hk).
  Qed.

  Definition src_number_schedule_changes_widen : Prop :=
    ltac:(body_of (fun s : S.statement_number_schedule_changes_widen => s Job)).
  Definition tgt_number_schedule_changes_widen : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_number_schedule_changes_widen Job dJ)).
  Theorem number_schedule_changes_widen_correspondence :
    PropSPropRel src_number_schedule_changes_widen tgt_number_schedule_changes_widen.
  Proof.
    unfold src_number_schedule_changes_widen, tgt_number_schedule_changes_widen.
    cover_sched.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_nat_correspondence. intros u1R u1L Hu1.
    apply ar_forall_nat_correspondence. intros u2R u2L Hu2.
    imp (sub_nat_le_correspondence _ _ _ _ Ht1 Hu1).
    imp (sub_nat_le_correspondence _ _ _ _ Hu2 Ht2).
    exact (sub_nat_le_correspondence _ _ _ _
      (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Hu1 Hu2)
      (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Ht1 Ht2)).
  Qed.

  Definition src_same_scheduled_state_merge : Prop :=
    ltac:(body_of (fun s : S.statement_same_scheduled_state_merge => s Job)).
  Definition tgt_same_scheduled_state_merge : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_same_scheduled_state_merge Job dJ)).
  Theorem same_scheduled_state_merge_correspondence :
    PropSPropRel src_same_scheduled_state_merge tgt_same_scheduled_state_merge.
  Proof.
    unfold src_same_scheduled_state_merge, tgt_same_scheduled_state_merge.
    cover_sched.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ovhsc_forall_option. intros o1R o1L Ho1.
    apply ovhsc_forall_option. intros o2R o2L Ho2.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
         (ar_decide_lt_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2)))|].
    imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (schedule_change_correspondence Job sR sL Hsc _ _ Ht))).
    imp (ar_bool_truth_correspondence _ _
      (scheduled_job_invariant_correspondence Job sR sL Hsc _ _ _ _ _ _ Ho1 Ht1 Ht)).
    imp (ar_bool_truth_correspondence _ _
      (scheduled_job_invariant_correspondence Job sR sL Hsc _ _ _ _ _ _ Ho2 Ht Ht2)).
    exact (sc_option_eq_correspondence Job _ _ _ _ Ho1 Ho2).
  Qed.

  Definition src_no_schedule_changes_implies_constant_schedule : Prop :=
    ltac:(body_of (fun s : S.statement_no_schedule_changes_implies_constant_schedule => s Job)).
  Definition tgt_no_schedule_changes_implies_constant_schedule : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_no_schedule_changes_implies_constant_schedule Job dJ)).
  Theorem no_schedule_changes_implies_constant_schedule_correspondence :
    PropSPropRel src_no_schedule_changes_implies_constant_schedule
      tgt_no_schedule_changes_implies_constant_schedule.
  Proof.
    unfold src_no_schedule_changes_implies_constant_schedule, tgt_no_schedule_changes_implies_constant_schedule.
    cover_sched.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
         (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2)))|].
    imp (sub_nat_eq_correspondence _ _ _ _ (number_schedule_changes_correspondence Job sR sL Hsc _ _ _ _ Ht1 Ht2)
      (sub_nat_rel_canonical 0)).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (schedule_change_correspondence Job sR sL Hsc _ _ Ht))).
  Qed.

  Definition src_no_changes_implies_same_scheduled_job : Prop :=
    ltac:(body_of (fun s : S.statement_no_changes_implies_same_scheduled_job => s Job)).
  Definition tgt_no_changes_implies_same_scheduled_job : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_no_changes_implies_same_scheduled_job Job dJ)).
  Theorem no_changes_implies_same_scheduled_job_correspondence :
    PropSPropRel src_no_changes_implies_same_scheduled_job tgt_no_changes_implies_same_scheduled_job.
  Proof.
    unfold src_no_changes_implies_same_scheduled_job, tgt_no_changes_implies_same_scheduled_job.
    cover_sched.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros uR uL Hu.
    apply ovhsc_forall_option. intros oR oL Ho.
    imp (ar_bool_truth_correspondence _ _ (no_schedule_changes_during_correspondence Job sR sL Hsc _ _ _ _ Ht1 Ht2)).
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
         (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2)))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
         (ar_decide_le_related _ _ _ _ Ht1 Hu) (ar_decide_lt_related _ _ _ _ Hu Ht2)))|].
    imp (sc_option_eq_correspondence Job _ _ _ _ (sc_scheduled_job_correspondence Job sR sL tR tL Hsc Ht) Ho).
    exact (sc_option_eq_correspondence Job _ _ _ _ (sc_scheduled_job_correspondence Job sR sL uR uL Hsc Hu) Ho).
  Qed.
End Stmts.
