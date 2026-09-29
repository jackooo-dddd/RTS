From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import BlackoutBoundSemanticSource.
From prosa Require Import behavior.all model.processor.overheads model.processor.supply
  analysis.definitions.overheads.schedule_change.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheadsBlackoutBound ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence
  OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers
  OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers
  OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel.
From FoundationCertificates Require
  ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeCorrespondence
  OverheadsBaseAdapter OverheadsCorrespondence OverheadResourceModelCorrespondence.

Module I := ImportedOverheadsBlackoutBound.
Module S := BlackoutBoundSemanticSource.BlackoutBoundSemanticSource.
Module SCS := ScheduleChangeStateAdapter.
Module SCC := ScheduleChangeCorrespondence.
Module OVC := OverheadsCorrespondence.
Module ORM := OverheadResourceModelCorrespondence.

(** Statement correspondences for [analysis/facts/model/overheads/blackout_bound.v].

    Source side: the extracted statements specialised at the job type; target side: the imported Lean theorem
    types.  The overheads processor model is fixed on both sides and related by [ovh_psrel] (OvhStateRel.v, as in
    the accepted overheads-schedule certificate); the generic chain helpers are replayed at its universe instance
    (Ovh*.v, see their headers).  Schedules are covered in both directions through it; every related pair is also
    related by the accepted constructor-wise overheads relation [OvhScheduleRel] and schedule-change relation
    [ScScheduleRel] (both state maps are constructor-wise), which gives access to the accepted certificates of
    [scheduled_job], the [is_*] observations, [schedule_change], [number_schedule_changes],
    [no_schedule_changes_during] and the overhead-resource-model definitions.  Option jobs are covered in both
    directions by [ScOptionRel]; instants, durations and counts are related by [SubNatRel].  The supply-side
    constants ([blackout_during] through its kernel-guarded projection, [is_blackout], [has_supply],
    [supply_at]) are related through [supply_in] of [ovh_psrel]; the interval counts [total_time_in_*] through
    their kernel-guarded list-interval projections.  No source or target theorem is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

(** The Boolean relations of the adapters are the same map. *)
Lemma bob_sc_ar (b : bool) (bL : I.Bool) : ScheduleChangeBaseAdapter.ScBoolRel b bL -> ArBoolRel b bL.
Proof. intro H. destruct b; exact H. Qed.

Lemma bob_ovh_svc (b : bool) (bL : I.Bool) : OverheadsBaseAdapter.OvhBoolRel b bL -> SvcBoolRel b bL.
Proof. intro H. destruct b; exact H. Qed.

Lemma bob_svc_ar (b : bool) (bL : I.Bool) : SvcBoolRel b bL -> ArBoolRel b bL.
Proof. intro H. destruct b; exact H. Qed.

(** Boolean truth without an auxiliary SProp truth constant: the two Boolean constructors are discriminated
    through [Lean.eq] and the imported empty [False]. *)
Definition bob_bool_false_ne_true (E : Lean.eq I.Bool_false I.Bool_true) : I.False :=
  isj_lean_transport (fun b => match b with I.Bool_false => Lean.eq I.Bool_false I.Bool_false | I.Bool_true => I.False end)
    _ _ E (@Lean.eq_refl _ _).

Definition bob_false_to_strict (H : I.False) : StrictlyInhabited Logic.False := match H with end.

Lemma bob_bool_truth (bR : bool) (bL : I.Bool) :
  ArBoolRel bR bL -> PropSPropRel (is_true bR) (Lean.eq bL I.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (bob_false_to_strict (bob_bool_false_ne_true (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition bob_opt_from {T : Type} (y : I.Option T) : option T :=
  match y with I.Option_some j => Some j | I.Option_none => None end.

Lemma bob_opt_from_rel {T : Type} (y : I.Option T) : SCS.ScOptionRel (bob_opt_from y) y.
Proof. destruct y; exact (@Lean.eq_refl _ _). Qed.

Lemma bob_exists_option (Job : eqType) (P : option Job -> Prop) (Q : I.Option Job -> SProp) :
  (forall oR oL, SCS.ScOptionRel oR oL -> PropSPropRel (P oR) (Q oL)) ->
  PropSPropRel (exists o, P o) (I.Exists (I.Option Job) Q).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [o Ho].
    exact (I.Exists_intro _ Q (SCS.sc_option_to_imported o) (prop_to_sprop _ _ (H _ _ (@Lean.eq_refl _ _)) Ho)).
  - intros [oL HoL]. apply strictly_inhabits. exists (bob_opt_from oL).
    exact (sprop_to_prop _ _ (H _ _ (bob_opt_from_rel oL)) HoL).
Qed.

Section Stmts.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.overheads.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Overheads_processor_state Job dJ.
  Let X := ovh_psrel Job.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Section Pair.
    Variable sR : @prosa.behavior.schedule.schedule Job PR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PL.
    Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

    Lemma bob_ovh_sched : OVC.OvhScheduleRel Job sR sL.
    Proof.
      intros tR tL Ht.
      refine (sub_imported_eq_trans _ _ _ _ (Hs tR tL Ht)). cbn.
      destruct (sR tR) as [| a b | a | j | j]; cbn; try destruct a; try destruct b; exact (@Lean.eq_refl _ _).
    Qed.

    Lemma bob_sc_sched : SCS.ScScheduleRel Job sR sL.
    Proof.
      intros tR tL Ht.
      refine (sub_imported_eq_trans _ _ _ _ (Hs tR tL Ht)). cbn.
      destruct (sR tR) as [| a b | a | j | j]; cbn; try destruct a; try destruct b; exact (@Lean.eq_refl _ _).
    Qed.

    Lemma bob_supply_at_related tR tL :
      SubNatRel tR tL ->
      SubNatRel (@prosa.model.processor.supply.supply_at Job PR sR tR)
        (I.Prosa_Validation_SupplyInterface_supplyAtProjection_inst4 Job dJ PL sL tL).
    Proof.
      intro Ht. unfold prosa.model.processor.supply.supply_at.
      cbn [I.Prosa_Validation_SupplyInterface_supplyAtProjection_inst4].
      exact (isj_lean_transport
        (fun s => SubNatRel (@prosa.behavior.schedule.supply_in Job PR (sR tR))
           (I.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4 Job dJ PL s))
        _ _ (Hs tR tL Ht) (isj_sup_in_rel Job PR PL X (sR tR))).
    Qed.

    Lemma bob_is_blackout_related tR tL :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.model.processor.supply.is_blackout Job PR sR tR)
        (I.Prosa_Validation_SupplyInterface_isBlackoutProjection_inst4 Job dJ PL sL tL).
    Proof.
      intro Ht. unfold prosa.model.processor.supply.is_blackout, prosa.model.processor.supply.has_supply.
      cbn [I.Prosa_Validation_SupplyInterface_isBlackoutProjection_inst4
        I.Prosa_Validation_SupplyInterface_hasSupplyProjection_inst4].
      exact (svc_bool_not_related _ _ (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0)
        (bob_supply_at_related tR tL Ht))).
    Qed.

    Lemma bob_blackout_related t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.model.processor.supply.blackout_during Job PR sR t1R t2R)
        (I.Prosa_Model_Processor_Supply_blackout_during_inst4 Job dJ PL sL t1L t2L).
    Proof.
      intros H1 H2. unfold prosa.model.processor.supply.blackout_during.
      apply svc_interval_sum_related; [exact H1|exact H2|].
      intros tR tL Ht. exact (isj_bool_to_nat_related _ _ (bob_is_blackout_related tR tL Ht)).
    Qed.

    Local Ltac total obs := intros H1 H2;
      unfold prosa.model.processor.overheads.total_time_in_dispatch,
        prosa.model.processor.overheads.total_time_in_context_switch,
        prosa.model.processor.overheads.total_time_in_CRPD;
      apply svc_interval_sum_related; [exact H1|exact H2|];
      intros tR tL Ht; exact (isj_bool_to_nat_related _ _ (bob_ovh_svc _ _ (obs Job sR sL tR tL bob_ovh_sched Ht))).

    Lemma bob_total_dispatch_related t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.model.processor.overheads.total_time_in_dispatch Job sR t1R t2R)
        (I.Prosa_Model_Processor_Overheads_total_time_in_dispatch Job dJ sL t1L t2L).
    Proof. total OVC.ovh_is_dispatch_correspondence. Qed.

    Lemma bob_total_context_switch_related t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.model.processor.overheads.total_time_in_context_switch Job sR t1R t2R)
        (I.Prosa_Model_Processor_Overheads_total_time_in_context_switch Job dJ sL t1L t2L).
    Proof. total OVC.ovh_is_context_switch_correspondence. Qed.

    Lemma bob_total_CRPD_related t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.model.processor.overheads.total_time_in_CRPD Job sR t1R t2R)
        (I.Prosa_Model_Processor_Overheads_total_time_in_CRPD Job dJ sL t1L t2L).
    Proof. total OVC.ovh_is_CRPD_correspondence. Qed.

    Lemma bob_nsc_truth t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      PropSPropRel
        (is_true (@prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during Job sR t1R t2R))
        (Lean.eq (I.Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during Job dJ sL t1L t2L)
          I.Bool_true).
    Proof.
      intros H1 H2.
      exact (bob_bool_truth _ _
        (bob_sc_ar _ _ (SCC.no_schedule_changes_during_correspondence Job sR sL bob_sc_sched _ _ _ _ H1 H2))).
    Qed.

    Lemma bob_sc_truth tR tL :
      SubNatRel tR tL ->
      PropSPropRel (is_true (@prosa.analysis.definitions.overheads.schedule_change.schedule_change Job sR tR))
        (Lean.eq (I.Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change Job dJ sL tL) I.Bool_true).
    Proof.
      intro Ht.
      exact (bob_bool_truth _ _
        (bob_sc_ar _ _ (SCC.schedule_change_correspondence Job sR sL bob_sc_sched _ _ Ht))).
    Qed.

    Lemma bob_count_related t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes Job sR t1R t2R)
        (I.Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job dJ sL t1L t2L).
    Proof.
      intros H1 H2. exact (SCC.number_schedule_changes_correspondence Job sR sL bob_sc_sched _ _ _ _ H1 H2).
    Qed.
  End Pair.

  Local Ltac pre sR sL Hs := apply (fpre_forall_sched Job PR PL X); intros sR sL Hs.
  Local Ltac orm sR sL Hs DR DL HD CR CL HC PR' PL' HP :=
    apply ar_forall_nat_correspondence; intros DR DL HD;
    apply ar_forall_nat_correspondence; intros CR CL HC;
    apply ar_forall_nat_correspondence; intros PR' PL' HP;
    imp (ORM.overhead_resource_model_correspondence Job sR sL (bob_ovh_sched sR sL Hs) _ _ _ _ _ _ HD HC HP).
  Local Ltac nats a b H := apply ar_forall_nat_correspondence; intros a b H.

  Definition src_blackout_during_split : Prop :=
    ltac:(body_of (fun s : S.statement_blackout_during_split => s Job)).
  Definition tgt_blackout_during_split : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_blackout_during_split Job dJ)).
  Theorem blackout_during_split_correspondence : PropSPropRel src_blackout_during_split tgt_blackout_during_split.
  Proof.
    unfold src_blackout_during_split, tgt_blackout_during_split.
    pre sR sL Hs. nats t1R t1L H1. nats t2R t2L H2.
    exact (sub_nat_eq_correspondence _ _ _ _ (bob_blackout_related sR sL Hs _ _ _ _ H1 H2)
      (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _
        (bob_total_dispatch_related sR sL Hs _ _ _ _ H1 H2) (bob_total_context_switch_related sR sL Hs _ _ _ _ H1 H2))
        (bob_total_CRPD_related sR sL Hs _ _ _ _ H1 H2))).
  Qed.

  Local Ltac eqjob total spent sR sL Hs t1R t1L H1 t2R t2L H2 oR oL Ho :=
    pre sR sL Hs; nats t1R t1L H1; nats t2R t2L H2;
    imp (bob_nsc_truth sR sL Hs _ _ _ _ H1 H2);
    apply (bob_exists_option Job); intros oR oL Ho;
    exact (sub_nat_eq_correspondence _ _ _ _ (total sR sL Hs _ _ _ _ H1 H2)
      (spent Job sR sL (bob_ovh_sched sR sL Hs) oR oL _ _ _ _ Ho H1 H2)).

  Definition src_total_dispatch_time_eq_job_dispatch_time : Prop :=
    ltac:(body_of (fun s : S.statement_total_dispatch_time_eq_job_dispatch_time => s Job)).
  Definition tgt_total_dispatch_time_eq_job_dispatch_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_total_dispatch_time_eq_job_dispatch_time Job dJ)).
  Theorem total_dispatch_time_eq_job_dispatch_time_correspondence :
    PropSPropRel src_total_dispatch_time_eq_job_dispatch_time tgt_total_dispatch_time_eq_job_dispatch_time.
  Proof.
    unfold src_total_dispatch_time_eq_job_dispatch_time, tgt_total_dispatch_time_eq_job_dispatch_time.
    eqjob bob_total_dispatch_related ORM.time_spent_in_dispatch_correspondence sR sL Hs t1R t1L H1 t2R t2L H2 oR oL Ho.
  Qed.

  Definition src_total_cswitch_time_eq_job_cswitch_time : Prop :=
    ltac:(body_of (fun s : S.statement_total_cswitch_time_eq_job_cswitch_time => s Job)).
  Definition tgt_total_cswitch_time_eq_job_cswitch_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_total_cswitch_time_eq_job_cswitch_time Job dJ)).
  Theorem total_cswitch_time_eq_job_cswitch_time_correspondence :
    PropSPropRel src_total_cswitch_time_eq_job_cswitch_time tgt_total_cswitch_time_eq_job_cswitch_time.
  Proof.
    unfold src_total_cswitch_time_eq_job_cswitch_time, tgt_total_cswitch_time_eq_job_cswitch_time.
    eqjob bob_total_context_switch_related ORM.time_spent_in_context_switch_correspondence sR sL Hs t1R t1L H1 t2R t2L H2 oR oL Ho.
  Qed.

  Definition src_total_CRPD_time_eq_job_CRPD_time : Prop :=
    ltac:(body_of (fun s : S.statement_total_CRPD_time_eq_job_CRPD_time => s Job)).
  Definition tgt_total_CRPD_time_eq_job_CRPD_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_total_CRPD_time_eq_job_CRPD_time Job dJ)).
  Theorem total_CRPD_time_eq_job_CRPD_time_correspondence :
    PropSPropRel src_total_CRPD_time_eq_job_CRPD_time tgt_total_CRPD_time_eq_job_CRPD_time.
  Proof.
    unfold src_total_CRPD_time_eq_job_CRPD_time, tgt_total_CRPD_time_eq_job_CRPD_time.
    eqjob bob_total_CRPD_related ORM.time_spent_in_CRPD_correspondence sR sL Hs t1R t1L H1 t2R t2L H2 oR oL Ho.
  Qed.

  Definition src_total_time_in_dispatch_is_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_total_time_in_dispatch_is_bounded => s Job)).
  Definition tgt_total_time_in_dispatch_is_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_total_time_in_dispatch_is_bounded Job dJ)).
  Theorem total_time_in_dispatch_is_bounded_correspondence :
    PropSPropRel src_total_time_in_dispatch_is_bounded tgt_total_time_in_dispatch_is_bounded.
  Proof.
    unfold src_total_time_in_dispatch_is_bounded, tgt_total_time_in_dispatch_is_bounded.
    pre sR sL Hs. orm sR sL Hs DR DL HD CR CL HC PR' PL' HP.
    nats t1R t1L H1. nats t2R t2L H2.
    imp (bob_nsc_truth sR sL Hs _ _ _ _ H1 H2).
    exact (sub_nat_le_correspondence _ _ _ _ (bob_total_dispatch_related sR sL Hs _ _ _ _ H1 H2) HD).
  Qed.

  Definition src_total_time_in_cswitch_is_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_total_time_in_cswitch_is_bounded => s Job)).
  Definition tgt_total_time_in_cswitch_is_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_total_time_in_cswitch_is_bounded Job dJ)).
  Theorem total_time_in_cswitch_is_bounded_correspondence :
    PropSPropRel src_total_time_in_cswitch_is_bounded tgt_total_time_in_cswitch_is_bounded.
  Proof.
    unfold src_total_time_in_cswitch_is_bounded, tgt_total_time_in_cswitch_is_bounded.
    pre sR sL Hs. orm sR sL Hs DR DL HD CR CL HC PR' PL' HP.
    nats t1R t1L H1. nats t2R t2L H2.
    imp (bob_nsc_truth sR sL Hs _ _ _ _ H1 H2).
    exact (sub_nat_le_correspondence _ _ _ _ (bob_total_context_switch_related sR sL Hs _ _ _ _ H1 H2) HC).
  Qed.

  Definition src_total_time_in_CRPD_is_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_total_time_in_CRPD_is_bounded => s Job)).
  Definition tgt_total_time_in_CRPD_is_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_total_time_in_CRPD_is_bounded Job dJ)).
  Theorem total_time_in_CRPD_is_bounded_correspondence :
    PropSPropRel src_total_time_in_CRPD_is_bounded tgt_total_time_in_CRPD_is_bounded.
  Proof.
    unfold src_total_time_in_CRPD_is_bounded, tgt_total_time_in_CRPD_is_bounded.
    pre sR sL Hs. orm sR sL Hs DR DL HD CR CL HC PR' PL' HP.
    nats t1R t1L H1. nats t2R t2L H2.
    imp (bob_nsc_truth sR sL Hs _ _ _ _ H1 H2).
    exact (sub_nat_le_correspondence _ _ _ _ (bob_total_CRPD_related sR sL Hs _ _ _ _ H1 H2) HP).
  Qed.

  Definition src_no_sched_changes_bounded_overheads_blackout : Prop :=
    ltac:(body_of (fun s : S.statement_no_sched_changes_bounded_overheads_blackout => s Job)).
  Definition tgt_no_sched_changes_bounded_overheads_blackout : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_no_sched_changes_bounded_overheads_blackout Job dJ)).
  Theorem no_sched_changes_bounded_overheads_blackout_correspondence :
    PropSPropRel src_no_sched_changes_bounded_overheads_blackout tgt_no_sched_changes_bounded_overheads_blackout.
  Proof.
    unfold src_no_sched_changes_bounded_overheads_blackout, tgt_no_sched_changes_bounded_overheads_blackout.
    pre sR sL Hs. orm sR sL Hs DR DL HD CR CL HC PR' PL' HP.
    nats t1R t1L H1. nats t2R t2L H2.
    imp (bob_nsc_truth sR sL Hs _ _ _ _ H1 H2).
    exact (sub_nat_le_correspondence _ _ _ _ (bob_blackout_related sR sL Hs _ _ _ _ H1 H2)
      (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HD HC) HP)).
  Qed.

  Definition src_sched_changes_start_busy_pref_bounded_overheads_blackout : Prop :=
    ltac:(body_of (fun s : S.statement_sched_changes_start_busy_pref_bounded_overheads_blackout => s Job)).
  Definition tgt_sched_changes_start_busy_pref_bounded_overheads_blackout : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_sched_changes_start_busy_pref_bounded_overheads_blackout Job dJ)).
  Theorem sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence :
    PropSPropRel src_sched_changes_start_busy_pref_bounded_overheads_blackout
      tgt_sched_changes_start_busy_pref_bounded_overheads_blackout.
  Proof.
    unfold src_sched_changes_start_busy_pref_bounded_overheads_blackout,
      tgt_sched_changes_start_busy_pref_bounded_overheads_blackout.
    pre sR sL Hs. orm sR sL Hs DR DL HD CR CL HC PR' PL' HP.
    nats t1R t1L H1. nats t2R t2L H2.
    imp (sub_nat_eq_correspondence _ _ _ _ (bob_count_related sR sL Hs _ _ _ _ H1 H2) (sub_nat_rel_canonical 1)).
    imp (bob_sc_truth sR sL Hs _ _ H1).
    exact (sub_nat_le_correspondence _ _ _ _ (bob_blackout_related sR sL Hs _ _ _ _ H1 H2)
      (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HD HC) HP)).
  Qed.

  Definition src_fin_sched_changes_start_busy_pref_bounded_overheads_blackout : Prop :=
    ltac:(body_of (fun s : S.statement_fin_sched_changes_start_busy_pref_bounded_overheads_blackout => s Job)).
  Definition tgt_fin_sched_changes_start_busy_pref_bounded_overheads_blackout : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_fin_sched_changes_start_busy_pref_bounded_overheads_blackout Job dJ)).
  Theorem fin_sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence :
    PropSPropRel src_fin_sched_changes_start_busy_pref_bounded_overheads_blackout
      tgt_fin_sched_changes_start_busy_pref_bounded_overheads_blackout.
  Proof.
    unfold src_fin_sched_changes_start_busy_pref_bounded_overheads_blackout,
      tgt_fin_sched_changes_start_busy_pref_bounded_overheads_blackout.
    pre sR sL Hs. orm sR sL Hs DR DL HD CR CL HC PR' PL' HP.
    nats kR kL Hk. nats t1R t1L H1. nats t2R t2L H2.
    imp (bob_sc_truth sR sL Hs _ _ H1).
    imp (sub_nat_eq_correspondence _ _ _ _ (bob_count_related sR sL Hs _ _ _ _ H1 H2) Hk).
    exact (sub_nat_le_correspondence _ _ _ _ (bob_blackout_related sR sL Hs _ _ _ _ H1 H2)
      (sub_mul_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HD HC) HP) Hk)).
  Qed.

  Definition src_finite_sched_changes_bounded_overheads_blackout : Prop :=
    ltac:(body_of (fun s : S.statement_finite_sched_changes_bounded_overheads_blackout => s Job)).
  Definition tgt_finite_sched_changes_bounded_overheads_blackout : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_finite_sched_changes_bounded_overheads_blackout Job dJ)).
  Theorem finite_sched_changes_bounded_overheads_blackout_correspondence :
    PropSPropRel src_finite_sched_changes_bounded_overheads_blackout tgt_finite_sched_changes_bounded_overheads_blackout.
  Proof.
    unfold src_finite_sched_changes_bounded_overheads_blackout, tgt_finite_sched_changes_bounded_overheads_blackout.
    pre sR sL Hs. orm sR sL Hs DR DL HD CR CL HC PR' PL' HP.
    nats kR kL Hk. nats t1R t1L H1. nats t2R t2L H2.
    imp (sub_nat_eq_correspondence _ _ _ _ (bob_count_related sR sL Hs _ _ _ _ (pp_succ_related _ _ H1) H2) Hk).
    exact (sub_nat_le_correspondence _ _ _ _ (bob_blackout_related sR sL Hs _ _ _ _ H1 H2)
      (sub_mul_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HD HC) HP)
        (sub_add_correspondence _ _ _ _ Hk (sub_nat_rel_canonical 1)))).
  Qed.
End Stmts.
