From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsServiceSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsService ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations FsvcScheduledHelpers.

Module I := ImportedFactsService.
Module S := FactsServiceSemanticSource.FactsServiceSemanticSource.

(** Statement correspondences for [analysis/facts/behavior/service.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading input binders ([Job], [ProcessorState], and where they precede
    every hypothesis the schedule(s), job, [JobArrival] and arrival
    sequence).  Target side: the type of the imported Lean theorem.

    Input relations: the two-sided processor-state relation
    [SvcProcessorStateRel] extended by its [supply_on] field ([FsvSupplyRel];
    the accepted relation relates [scheduled_on] and [service_on] only), the
    pointwise schedule relation, [ArJobArrivalRel], [ArArrivalSequenceRel].
    Schedules, states, arrival sequences, instants and jobs occurring after a
    hypothesis are covered in both directions.  For the two statements that
    compare processor *states* for equality, the state relation is required
    to be the graph of its bijection ([FsvStateGraph]). *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Arithmetic and Boolean helpers *)

Lemma fsv_succ_related (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> SubNatRel nR.+1 (sub_imported_add nL (Lean.Nat_succ Lean.Nat_zero)).
Proof.
  intro Hn. rewrite -addn1.
  exact (sub_add_correspondence nR nL 1 (Lean.Nat_succ Lean.Nat_zero) Hn (sub_nat_rel_canonical 1)).
Qed.

Lemma fsv_range_le_lt aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (leq aR bR && ltn bR cR))
    (Lean.eq (I.Bool_and (ar_target_decide_le aL bL) (ar_target_decide_lt bL cL)) I.Bool_true).
Proof.
  intros Ha Hb Hc. apply ar_bool_truth_correspondence.
  exact (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ha Hb)
    (ar_decide_lt_related _ _ _ _ Hb Hc)).
Qed.

Lemma fsv_range_le_le aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (leq aR bR && leq bR cR))
    (Lean.eq (I.Bool_and (ar_target_decide_le aL bL) (ar_target_decide_le bL cL)) I.Bool_true).
Proof.
  intros Ha Hb Hc. apply ar_bool_truth_correspondence.
  exact (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ha Hb)
    (ar_decide_le_related _ _ _ _ Hb Hc)).
Qed.

Lemma fsv_bool_eq_correspondence aR aL bR bL :
  ArBoolRel aR aL -> ArBoolRel bR bL -> PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq. exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits.
    have Hc : Lean.eq (ar_bool_to_imported aR) (ar_bool_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hb)).
    have Hd := f_equal ar_bool_to_rocq (imported_eq_to_coq_eq _ _ Hc).
    rewrite !ar_bool_source_roundtrip in Hd. exact Hd.
Qed.

(** MathComp's finite Boolean existential over ['I_n] is [has] over [iota 0 n]. *)
Lemma fsv_exists_ord_has (n : nat) (p : nat -> bool) :
  [exists t : 'I_n, p t] = has p (iota 0 n).
Proof.
  apply/idP/idP.
  - move/existsP=> [[t lt] Hp]. apply/hasP. exists t => //. by rewrite mem_iota.
  - move/hasP=> [t]. rewrite mem_iota add0n => /andP [_ lt] Hp.
    apply/existsP. by exists (Ordinal lt).
Qed.


Lemma fsv_bool_or_related aR aL bR bL :
  ArBoolRel aR aL -> ArBoolRel bR bL -> ArBoolRel (aR || bR) (I.Bool_or aL bL).
Proof.
  intros Ha Hb. destruct aR, bR; cbn in *;
    destruct aL, bL; try exact (@Lean.eq_refl _ _);
    try exact (ar_false_elim _ (ar_false_ne_true Ha));
    try exact (ar_false_elim _ (ar_false_ne_true Hb));
    try exact (ar_false_elim _ (ar_false_ne_true (sub_imported_eq_sym _ _ Ha)));
    try exact (ar_false_elim _ (ar_false_ne_true (sub_imported_eq_sym _ _ Hb))).
Qed.

Fixpoint fsv_any_nat_canonical (pR : nat -> bool) (pL : Lean.Nat -> I.Bool)
    (Hp : forall x, ArBoolRel (pR x) (pL (sub_nat_to_imported x))) (xs : seq nat) {struct xs} :
    ArBoolRel (has pR xs) (I.List_any_inst1 Lean.Nat (svc_nat_list_to_imported xs) pL) :=
  match xs return ArBoolRel (has pR xs) (I.List_any_inst1 Lean.Nat (svc_nat_list_to_imported xs) pL) with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => fsv_bool_or_related _ _ _ _ (Hp x) (fsv_any_nat_canonical pR pL Hp tail)
  end.

(** ** Processor-state and schedule operations *)

Section Operations.
  Context (Job : eqType).
  Let d := svc_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job d.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let StateR := @prosa.behavior.schedule.State Job PStateR.
  Let StateL := I.Prosa_Behavior_Schedule_ProcessorState_State Job d PStateL.
  Let SR := SvcScheduleRel Job PStateR PStateL R.

  (** The [supply_on] field of the processor-state relation (the accepted
      [SvcProcessorStateRel] relates [scheduled_on] and [service_on]). *)
  Definition FsvSupplyRel : SProp :=
    forall (sR : StateR) (sL : StateL) (cR : @prosa.behavior.schedule.Core Job PStateR),
      svc_ps_state_rel Job PStateR PStateL R sR sL ->
      SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job d PStateL sL
          (svc_ps_core_to_target Job PStateR PStateL R cR)).

  (** For state equalities: the state relation is the graph of its bijection. *)
  Definition FsvStateGraph : SProp :=
    forall (sR : StateR) (sL : StateL), svc_ps_state_rel Job PStateR PStateL R sR sL ->
      Lean.eq (svc_ps_state_to_target Job PStateR PStateL R sR) sL.

  Lemma fsv_state_eq_correspondence (Hg : FsvStateGraph) s1R s1L s2R s2L :
    svc_ps_state_rel Job PStateR PStateL R s1R s1L ->
    svc_ps_state_rel Job PStateR PStateL R s2R s2L ->
    PropSPropRel (s1R = s2R) (Lean.eq s1L s2L).
  Proof.
    intros H1 H2. apply prop_sprop_rel_intro.
    - intro Heq. destruct Heq.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (Hg _ _ H1)) (Hg _ _ H2)).
    - intro HL. apply strictly_inhabits.
      have Ht : Lean.eq (svc_ps_state_to_target Job PStateR PStateL R s1R)
          (svc_ps_state_to_target Job PStateR PStateL R s2R) :=
        sub_imported_eq_trans _ _ _ (Hg _ _ H1)
          (sub_imported_eq_trans _ _ _ HL (sub_imported_eq_sym _ _ (Hg _ _ H2))).
      have Hs := f_equal (svc_ps_state_to_source Job PStateR PStateL R) (imported_eq_to_coq_eq _ _ Ht).
      rewrite !(svc_ps_state_source_roundtrip Job PStateR PStateL R) in Hs.
      exact Hs.
  Qed.

  Hypothesis Hsupply : FsvSupplyRel.

  Lemma fsv_supply_in_related (sR : StateR) (sL : StateL) :
    svc_ps_state_rel Job PStateR PStateL R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_in Job PStateR sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job d PStateL sL).
  Proof.
    intro Hstate.
    have Hsum := svc_finite_sum_related _ _
      (svc_ps_core_to_target Job PStateR PStateL R)
      (fun cR => @prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (fun cL => I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job d PStateL sL cL)
      (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job d PStateL)
      (fun cR => Hsupply sR sL cR Hstate)
      (svc_ps_core_enumeration_rel Job PStateR PStateL R).
    unfold SubNatRel in Hsum |- *.
    exact (sub_imported_eq_trans _ _ _ Hsum
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ScheduleInterface_production_supply_in_as_list_sum Job d PStateL sL))).
  Qed.

  Lemma fsv_service_in_state (j : Job) (sR : StateR) (sL : StateL) :
    svc_ps_state_rel Job PStateR PStateL R sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_in Job PStateR j sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job d PStateL j sL).
  Proof. exact (svc_service_in_related Job PStateR PStateL R j sR sL). Qed.

  Theorem fsv_unit_service_related :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job d PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
    apply ar_forall_identity_correspondence => j.
    apply (fs_forall_state Job PStateR PStateL R) => sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (fsv_service_in_state j _ _ Hs) (sub_nat_rel_canonical 1)).
  Qed.

  Section WithSchedule.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
    Hypothesis Hsched : SR schedR schedL.

    Lemma fsv_service_at_related (j : Job) tR tL :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service_at Job d PStateL schedL j tL).
    Proof. exact (fs_service_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL). Qed.

    Lemma fsv_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
        (I.Prosa_Behavior_Service_service_during Job d PStateL schedL j t1L t2L).
    Proof.
      intros Ht1 Ht2.
      have Hsum := svc_interval_sum_related t1R t2R t1L t2L
        (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
        (fun t => I.Prosa_Behavior_Service_service_at Job d PStateL schedL j t)
        Ht1 Ht2 (fun tR tL Ht => fsv_service_at_related j tR tL Ht).
      change (SubNatRel
        (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
        (I.Prosa_Validation_ServiceInterface_serviceDuringProjection Job d PStateL schedL j t1L t2L)) in Hsum.
      exact Hsum.
    Qed.

    Lemma fsv_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service Job d PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service.
      cbn [I.Prosa_Behavior_Service_service].
      exact (fsv_service_during_related j O tR Lean.Nat_zero tL (sub_nat_rel_canonical O) Ht).
    Qed.

    Lemma fsv_receives_related (j : Job) tR tL :
      SubNatRel tR tL ->
      ArBoolRel (@prosa.behavior.service.receives_service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_receives_service_at Job d PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.receives_service_at.
      cbn [I.Prosa_Behavior_Service_receives_service_at].
      exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (fsv_service_at_related j tR tL Ht)).
    Qed.

    Lemma fsv_supply_at_related tR tL :
      SubNatRel tR tL ->
      SubNatRel (@prosa.model.processor.supply.supply_at Job PStateR schedR tR)
        (I.Prosa_Model_Processor_Supply_supply_at Job d PStateL schedL tL).
    Proof. intro Ht. exact (fsv_supply_in_related _ _ (Hsched tR tL Ht)). Qed.

    Lemma fsv_has_supply_related tR tL :
      SubNatRel tR tL ->
      ArBoolRel (@prosa.model.processor.supply.has_supply Job PStateR schedR tR)
        (I.Prosa_Model_Processor_Supply_has_supply Job d PStateL schedL tL).
    Proof.
      intro Ht.
      exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (fsv_supply_at_related tR tL Ht)).
    Qed.

    Lemma fsv_is_blackout_related tR tL :
      SubNatRel tR tL ->
      ArBoolRel (@prosa.model.processor.supply.is_blackout Job PStateR schedR tR)
        (I.Prosa_Model_Processor_Supply_is_blackout Job d PStateL schedL tL).
    Proof. intro Ht. exact (svc_bool_not_related _ _ (fsv_has_supply_related tR tL Ht)). Qed.
  End WithSchedule.

  Theorem fsv_fully_consuming_related :
    PropSPropRel (@prosa.model.processor.platform_properties.fully_consuming_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job d PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model].
    apply ar_forall_identity_correspondence => j.
    apply (fs_forall_schedule Job PStateR PStateL R) => sR sL Hs.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence;
      [exact (fs_scheduled_at_truth Job PStateR PStateL R sR sL Hs j tR tL Ht)|].
    exact (sub_nat_eq_correspondence _ _ _ _ (fsv_service_at_related sR sL Hs j tR tL Ht)
      (fsv_supply_at_related sR sL Hs tR tL Ht)).
  Qed.
End Operations.

Lemma fsv_unit_growth_related (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  (forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL)) ->
  PropSPropRel (prosa.util.unit_growth.unit_growth_function fR)
    (I.Prosa_Util_UnitGrowth_unit_growth_function fL).
Proof.
  intro Hf. unfold prosa.util.unit_growth.unit_growth_function.
  cbn [I.Prosa_Util_UnitGrowth_unit_growth_function].
  apply ar_forall_nat_correspondence => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _
    (Hf _ _ (sub_add_correspondence _ _ _ _ Ht (sub_nat_rel_canonical 1)))
    (sub_add_correspondence _ _ _ _ (Hf _ _ Ht) (sub_nat_rel_canonical 1))).
Qed.

Lemma fsv_exists_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists n, PR n) (I.Exists Lean.Nat PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [n Hn]. exact (I.Exists_intro Lean.Nat PL (sub_nat_to_imported n)
      (prop_to_sprop _ _ (H n _ (sub_nat_rel_canonical n)) Hn)).
  - intros [nL HnL]. apply strictly_inhabits. exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _ (H _ nL (sub_nat_rel_surjective nL)) HnL).
Qed.

Lemma fsv_lt0 aR aL : SubNatRel aR aL ->
  PropSPropRel (is_true (ltn O aR)) (sub_imported_lt Lean.Nat_zero aL).
Proof. intro Ha. exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Ha). Qed.

Lemma fsv_eq0 aR aL : SubNatRel aR aL -> PropSPropRel (Logic.eq aR O) (Lean.eq aL Lean.Nat_zero).
Proof. intro Ha. exact (sub_nat_eq_correspondence _ _ _ _ Ha (sub_nat_rel_canonical O)). Qed.

Lemma fsv_exists_ord_related (nR : nat) (nL : Lean.Nat) (pR : nat -> bool) (pL : Lean.Nat -> I.Bool) :
  SubNatRel nR nL -> (forall xR xL, SubNatRel xR xL -> ArBoolRel (pR xR) (pL xL)) ->
  ArBoolRel [exists t : 'I_nR, pR t]
    (I.List_any_inst1 Lean.Nat (I.List_range' Lean.Nat_zero nL svc_target_one) pL).
Proof.
  intros Hn Hp. rewrite fsv_exists_ord_has.
  have Hl := svc_range_related O nR Lean.Nat_zero nL (sub_nat_rel_canonical O) Hn.
  refine (ari_lean_transport (fun l => ArBoolRel _ (I.List_any_inst1 Lean.Nat l pL)) _ _ Hl _).
  exact (fsv_any_nat_canonical pR pL (fun x => Hp x _ (sub_nat_rel_canonical x)) (iota O nR)).
Qed.

Section Statements.
  Context (Job : eqType).
  Let d := svc_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job d.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Let SR := SvcScheduleRel Job PStateR PStateL R.
  Let FS := fs_forall_schedule Job PStateR PStateL R.
  Let SA := fsv_service_at_related Job PStateR PStateL R.
  Let SD := fsv_service_during_related Job PStateR PStateL R.
  Let SV := fsv_service_related Job PStateR PStateL R.
  Let SCH := fs_scheduled_at_related Job PStateR PStateL R.
  Let SCT := fs_scheduled_at_truth Job PStateR PStateL R.
  Let RCV := fsv_receives_related Job PStateR PStateL R.
  Let UNIT := fsv_unit_service_related Job PStateR PStateL R.
  Let IDEAL := fs_ideal_progress_related Job PStateR PStateL R.
  Let NT bR bL H := fs_not_truth bR bL H.
  Let TR bR bL H := ar_bool_truth_correspondence bR bL H.
  Let LE := sub_nat_le_correspondence.
  Let LT := sub_nat_lt_correspondence.
  Let EQ := sub_nat_eq_correspondence.
  Let ADD := sub_add_correspondence.
  Let C := sub_nat_rel_canonical.

  (** *** Composition (inputs: schedule, job) *)
  Section Composition.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
    Hypothesis Hs : SR schedR schedL.
    Variable j : Job.

    Definition src_service_during_geq : Prop := ltac:(body_of (fun s : S.statement_service_during_geq => s Job PStateR schedR j)).
    Definition tgt_service_during_geq : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_geq Job d PStateL schedL j)).
    Theorem service_during_geq_correspondence : PropSPropRel src_service_during_geq tgt_service_during_geq.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H2 H1)|].
      exact (fsv_eq0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2)).
    Qed.

    Definition src_service_during_ge : Prop := ltac:(body_of (fun s : S.statement_service_during_ge => s Job PStateR schedR j)).
    Definition tgt_service_during_ge : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_ge Job d PStateL schedL j)).
    Theorem service_during_ge_correspondence : PropSPropRel src_service_during_ge tgt_service_during_ge.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_forall_nat_correspondence => kR kL Hk.
      apply ar_imp_correspondence; [exact (LT _ _ _ _ Hk (SD _ _ Hs j _ _ _ _ H1 H2))|].
      exact (LT _ _ _ _ H1 H2).
    Qed.

    Definition src_service0 : Prop := ltac:(body_of (fun s : S.statement_service0 => s Job PStateR schedR j)).
    Definition tgt_service0 : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service0 Job d PStateL schedL j)).
    Theorem service0_correspondence : PropSPropRel src_service0 tgt_service0.
    Proof. exact (fsv_eq0 _ _ (SV _ _ Hs j O Lean.Nat_zero (C O))). Qed.

    Definition src_service_during_instant : Prop := ltac:(body_of (fun s : S.statement_service_during_instant => s Job PStateR schedR j)).
    Definition tgt_service_during_instant : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_instant Job d PStateL schedL j)).
    Theorem service_during_instant_correspondence : PropSPropRel src_service_during_instant tgt_service_during_instant.
    Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      exact (EQ _ _ _ _ (SD _ _ Hs j _ _ _ _ Ht (fsv_succ_related _ _ Ht)) (SA _ _ Hs j _ _ Ht)).
    Qed.

    Definition src_service_during_cat : Prop := ltac:(body_of (fun s : S.statement_service_during_cat => s Job PStateR schedR j)).
    Definition tgt_service_during_cat : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_cat Job d PStateL schedL j)).
    Theorem service_during_cat_correspondence : PropSPropRel src_service_during_cat tgt_service_during_cat.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_forall_nat_correspondence => t3R t3L H3.
      apply ar_imp_correspondence; [exact (fsv_range_le_le _ _ _ _ _ _ H1 H2 H3)|].
      exact (EQ _ _ _ _ (ADD _ _ _ _ (SD _ _ Hs j _ _ _ _ H1 H2) (SD _ _ Hs j _ _ _ _ H2 H3))
        (SD _ _ Hs j _ _ _ _ H1 H3)).
    Qed.

    Definition src_service_cat : Prop := ltac:(body_of (fun s : S.statement_service_cat => s Job PStateR schedR j)).
    Definition tgt_service_cat : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_cat Job d PStateL schedL j)).
    Theorem service_cat_correspondence : PropSPropRel src_service_cat tgt_service_cat.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H1 H2)|].
      exact (EQ _ _ _ _ (ADD _ _ _ _ (SV _ _ Hs j _ _ H1) (SD _ _ Hs j _ _ _ _ H1 H2)) (SV _ _ Hs j _ _ H2)).
    Qed.

    Definition src_service_during_first_plus_later : Prop := ltac:(body_of (fun s : S.statement_service_during_first_plus_later => s Job PStateR schedR j)).
    Definition tgt_service_during_first_plus_later : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_first_plus_later Job d PStateL schedL j)).
    Theorem service_during_first_plus_later_correspondence : PropSPropRel src_service_during_first_plus_later tgt_service_during_first_plus_later.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LT _ _ _ _ H1 H2)|].
      exact (EQ _ _ _ _ (ADD _ _ _ _ (SA _ _ Hs j _ _ H1) (SD _ _ Hs j _ _ _ _ (fsv_succ_related _ _ H1) H2))
        (SD _ _ Hs j _ _ _ _ H1 H2)).
    Qed.

    Definition src_service_during_last_plus_before : Prop := ltac:(body_of (fun s : S.statement_service_during_last_plus_before => s Job PStateR schedR j)).
    Definition tgt_service_during_last_plus_before : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_last_plus_before Job d PStateL schedL j)).
    Theorem service_during_last_plus_before_correspondence : PropSPropRel src_service_during_last_plus_before tgt_service_during_last_plus_before.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H1 H2)|].
      exact (EQ _ _ _ _ (ADD _ _ _ _ (SD _ _ Hs j _ _ _ _ H1 H2) (SA _ _ Hs j _ _ H2))
        (SD _ _ Hs j _ _ _ _ H1 (fsv_succ_related _ _ H2))).
    Qed.

    Definition src_service_last_plus_before : Prop := ltac:(body_of (fun s : S.statement_service_last_plus_before => s Job PStateR schedR j)).
    Definition tgt_service_last_plus_before : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_last_plus_before Job d PStateL schedL j)).
    Theorem service_last_plus_before_correspondence : PropSPropRel src_service_last_plus_before tgt_service_last_plus_before.
    Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      exact (EQ _ _ _ _ (ADD _ _ _ _ (SV _ _ Hs j _ _ Ht) (SA _ _ Hs j _ _ Ht)) (SV _ _ Hs j _ _ (fsv_succ_related _ _ Ht))).
    Qed.

    Definition src_service_split_at_point : Prop := ltac:(body_of (fun s : S.statement_service_split_at_point => s Job PStateR schedR j)).
    Definition tgt_service_split_at_point : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_split_at_point Job d PStateL schedL j)).
    Theorem service_split_at_point_correspondence : PropSPropRel src_service_split_at_point tgt_service_split_at_point.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_forall_nat_correspondence => t3R t3L H3.
      apply ar_imp_correspondence; [exact (fsv_range_le_lt _ _ _ _ _ _ H1 H2 H3)|].
      exact (EQ _ _ _ _ (ADD _ _ _ _ (ADD _ _ _ _ (SD _ _ Hs j _ _ _ _ H1 H2) (SA _ _ Hs j _ _ H2))
          (SD _ _ Hs j _ _ _ _ (fsv_succ_related _ _ H2) H3))
        (SD _ _ Hs j _ _ _ _ H1 H3)).
    Qed.
  End Composition.

  (** *** Unit service (input: processor state; unit service is a hypothesis) *)
  Definition src_service_at_most_one : Prop := ltac:(body_of (fun s : S.statement_service_at_most_one => s Job PStateR)).
  Definition tgt_service_at_most_one : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_at_most_one Job d PStateL)).
  Theorem service_at_most_one_correspondence : PropSPropRel src_service_at_most_one tgt_service_at_most_one.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    exact (LE _ _ _ _ (SA _ _ Hs j _ _ Ht) (C 1)).
  Qed.

  Definition src_service_is_zero_or_one : Prop := ltac:(body_of (fun s : S.statement_service_is_zero_or_one => s Job PStateR)).
  Definition tgt_service_is_zero_or_one : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_is_zero_or_one Job d PStateL)).
  Theorem service_is_zero_or_one_correspondence : PropSPropRel src_service_is_zero_or_one tgt_service_is_zero_or_one.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply fs_or_correspondence; [exact (fsv_eq0 _ _ (SA _ _ Hs j _ _ Ht))|].
    exact (EQ _ _ _ _ (SA _ _ Hs j _ _ Ht) (C 1)).
  Qed.

  Definition src_cumulative_service_le_delta : Prop := ltac:(body_of (fun s : S.statement_cumulative_service_le_delta => s Job PStateR)).
  Definition tgt_cumulative_service_le_delta : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_cumulative_service_le_delta Job d PStateL)).
  Theorem cumulative_service_le_delta_correspondence : PropSPropRel src_cumulative_service_le_delta tgt_cumulative_service_le_delta.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_nat_correspondence => dR dL Hd.
    exact (LE _ _ _ _ (SD _ _ Hs j _ _ _ _ Ht (ADD _ _ _ _ Ht Hd)) Hd).
  Qed.

  Definition src_cumulative_service_ge_delta : Prop := ltac:(body_of (fun s : S.statement_cumulative_service_ge_delta => s Job PStateR)).
  Definition tgt_cumulative_service_ge_delta : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_cumulative_service_ge_delta Job d PStateL)).
  Theorem cumulative_service_ge_delta_correspondence : PropSPropRel src_cumulative_service_ge_delta tgt_cumulative_service_ge_delta.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_nat_correspondence => dR dL Hd.
    apply ar_forall_nat_correspondence => rR rL Hr.
    apply ar_imp_correspondence; [exact (LE _ _ _ _ Hr (SD _ _ Hs j _ _ _ _ Ht (ADD _ _ _ _ Ht Hd)))|].
    exact (LE _ _ _ _ Hr Hd).
  Qed.

  Definition src_service_during_is_unit_growth_function : Prop := ltac:(body_of (fun s : S.statement_service_during_is_unit_growth_function => s Job PStateR)).
  Definition tgt_service_during_is_unit_growth_function : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_is_unit_growth_function Job d PStateL)).
  Theorem service_during_is_unit_growth_function_correspondence : PropSPropRel src_service_during_is_unit_growth_function tgt_service_during_is_unit_growth_function.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    exact (fsv_unit_growth_related _ _ (fun nR nL Hn => SD _ _ Hs j _ _ _ _ Ht Hn)).
  Qed.

  Definition src_service_is_unit_growth_function : Prop := ltac:(body_of (fun s : S.statement_service_is_unit_growth_function => s Job PStateR)).
  Definition tgt_service_is_unit_growth_function : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_is_unit_growth_function Job d PStateL)).
  Theorem service_is_unit_growth_function_correspondence : PropSPropRel src_service_is_unit_growth_function tgt_service_is_unit_growth_function.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    exact (fsv_unit_growth_related _ _ (fun nR nL Hn => SV _ _ Hs j _ _ Hn)).
  Qed.

  Definition src_exists_intermediate_service_during : Prop := ltac:(body_of (fun s : S.statement_exists_intermediate_service_during => s Job PStateR)).
  Definition tgt_exists_intermediate_service_during : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_exists_intermediate_service_during Job d PStateL)).
  Theorem exists_intermediate_service_during_correspondence : PropSPropRel src_exists_intermediate_service_during tgt_exists_intermediate_service_during.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t0R t0L H0.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_nat_correspondence => xR xL Hx.
    apply ar_imp_correspondence; [exact (fsv_range_le_le _ _ _ _ _ _ H0 H1 H2)|].
    apply ar_imp_correspondence;
      [exact (fsv_range_le_lt _ _ _ _ _ _ (SD _ _ Hs j _ _ _ _ H0 H1) Hx (SD _ _ Hs j _ _ _ _ H0 H2))|].
    apply fsv_exists_nat => tR tL Ht.
    apply ar_and_correspondence; [exact (fsv_range_le_lt _ _ _ _ _ _ H1 Ht H2)|].
    exact (EQ _ _ _ _ (SD _ _ Hs j _ _ _ _ H0 Ht) Hx).
  Qed.

  Definition src_exists_intermediate_service : Prop := ltac:(body_of (fun s : S.statement_exists_intermediate_service => s Job PStateR)).
  Definition tgt_exists_intermediate_service : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_exists_intermediate_service Job d PStateL)).
  Theorem exists_intermediate_service_correspondence : PropSPropRel src_exists_intermediate_service tgt_exists_intermediate_service.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_nat_correspondence => xR xL Hx.
    apply ar_imp_correspondence; [exact (LT _ _ _ _ Hx (SV _ _ Hs j _ _ Ht))|].
    apply fsv_exists_nat => t'R t'L Ht'.
    apply ar_and_correspondence; [exact (LT _ _ _ _ Ht' Ht)|].
    exact (EQ _ _ _ _ (SV _ _ Hs j _ _ Ht') Hx).
  Qed.

  (** *** Fully consuming processors (supply field of the state relation) *)
  Section Supply.
    Hypothesis Hsupply : FsvSupplyRel Job PStateR PStateL R.
    Definition src_ideal_progress_inside_supplies : Prop := ltac:(body_of (fun s : S.statement_ideal_progress_inside_supplies => s Job PStateR)).
    Definition tgt_ideal_progress_inside_supplies : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_ideal_progress_inside_supplies Job d PStateL)).
    Theorem ideal_progress_inside_supplies_correspondence : PropSPropRel src_ideal_progress_inside_supplies tgt_ideal_progress_inside_supplies.
    Proof.
    apply ar_imp_correspondence; [exact (fsv_fully_consuming_related Job PStateR PStateL R Hsupply)|].
    apply FS => sR sL Hs. apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence;
      [exact (TR _ _ (fsv_has_supply_related Job PStateR PStateL R Hsupply sR sL Hs tR tL Ht))|].
    apply ar_imp_correspondence; [exact (SCT _ _ Hs j _ _ Ht)|].
    exact (TR _ _ (RCV _ _ Hs j _ _ Ht)).
  Qed.
    Section SupplySchedule.
      Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
      Variable schedL : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
      Hypothesis Hs : SR schedR schedL.
      Variable j : Job.
      Let HAS := fsv_has_supply_related Job PStateR PStateL R Hsupply schedR schedL Hs.
      Let BLK := fsv_is_blackout_related Job PStateR PStateL R Hsupply schedR schedL Hs.
      Definition src_receives_service_implies_has_supply : Prop := ltac:(body_of (fun s : S.statement_receives_service_implies_has_supply => s Job PStateR schedR j)).
      Definition tgt_receives_service_implies_has_supply : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_receives_service_implies_has_supply Job d PStateL schedL j)).
      Theorem receives_service_implies_has_supply_correspondence : PropSPropRel src_receives_service_implies_has_supply tgt_receives_service_implies_has_supply.
      Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (TR _ _ (RCV _ _ Hs j _ _ Ht))|].
      exact (TR _ _ (HAS _ _ Ht)).
    Qed.

      Definition src_no_blackout_when_service_received : Prop := ltac:(body_of (fun s : S.statement_no_blackout_when_service_received => s Job PStateR schedR j)).
      Definition tgt_no_blackout_when_service_received : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_no_blackout_when_service_received Job d PStateL schedL j)).
      Theorem no_blackout_when_service_received_correspondence : PropSPropRel src_no_blackout_when_service_received tgt_no_blackout_when_service_received.
      Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (TR _ _ (RCV _ _ Hs j _ _ Ht))|].
      exact (NT _ _ (BLK _ _ Ht)).
    Qed.

      Definition src_no_service_during_blackout : Prop := ltac:(body_of (fun s : S.statement_no_service_during_blackout => s Job PStateR schedR j)).
      Definition tgt_no_service_during_blackout : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_no_service_during_blackout Job d PStateL schedL j)).
      Theorem no_service_during_blackout_correspondence : PropSPropRel src_no_service_during_blackout tgt_no_service_during_blackout.
      Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (TR _ _ (BLK _ _ Ht))|].
      exact (fsv_eq0 _ _ (SA _ _ Hs j _ _ Ht)).
    Qed.
    End SupplySchedule.
  End Supply.

  (** *** Inputs: schedule and job *)
  Section SchedJob.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
    Hypothesis Hs : SR schedR schedL.
    Variable j : Job.
    Let RANGE t1R t1L tR tL t2R t2L H1 Ht H2 := fsv_range_le_lt t1R t1L tR tL t2R t2L H1 Ht H2.

    Definition src_service_monotonic : Prop := ltac:(body_of (fun s : S.statement_service_monotonic => s Job PStateR schedR j)).
    Definition tgt_service_monotonic : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_monotonic Job d PStateL schedL j)).
    Theorem service_monotonic_correspondence : PropSPropRel src_service_monotonic tgt_service_monotonic.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H1 H2)|].
      exact (LE _ _ _ _ (SV _ _ Hs j _ _ H1) (SV _ _ Hs j _ _ H2)).
    Qed.

    Definition src_not_scheduled_implies_no_service : Prop := ltac:(body_of (fun s : S.statement_not_scheduled_implies_no_service => s Job PStateR schedR j)).
    Definition tgt_not_scheduled_implies_no_service : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_not_scheduled_implies_no_service Job d PStateL schedL j)).
    Theorem not_scheduled_implies_no_service_correspondence : PropSPropRel src_not_scheduled_implies_no_service tgt_not_scheduled_implies_no_service.
    Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (NT _ _ (SCH _ _ Hs j _ _ Ht))|].
      exact (fsv_eq0 _ _ (SA _ _ Hs j _ _ Ht)).
    Qed.

    Definition src_not_scheduled_during_implies_zero_service : Prop := ltac:(body_of (fun s : S.statement_not_scheduled_during_implies_zero_service => s Job PStateR schedR j)).
    Definition tgt_not_scheduled_during_implies_zero_service : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_not_scheduled_during_implies_zero_service Job d PStateL schedL j)).
    Theorem not_scheduled_during_implies_zero_service_correspondence : PropSPropRel src_not_scheduled_during_implies_zero_service tgt_not_scheduled_during_implies_zero_service.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence.
      - apply ar_forall_nat_correspondence => tR tL Ht.
        apply ar_imp_correspondence; [exact (RANGE _ _ _ _ _ _ H1 Ht H2)|].
        exact (NT _ _ (SCH _ _ Hs j _ _ Ht)).
      - exact (fsv_eq0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2)).
    Qed.

    Definition src_service_at_implies_scheduled_at : Prop := ltac:(body_of (fun s : S.statement_service_at_implies_scheduled_at => s Job PStateR schedR j)).
    Definition tgt_service_at_implies_scheduled_at : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_at_implies_scheduled_at Job d PStateL schedL j)).
    Theorem service_at_implies_scheduled_at_correspondence : PropSPropRel src_service_at_implies_scheduled_at tgt_service_at_implies_scheduled_at.
    Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fsv_lt0 _ _ (SA _ _ Hs j _ _ Ht))|].
      exact (SCT _ _ Hs j _ _ Ht).
    Qed.

    Definition src_service_delta_implies_scheduled : Prop := ltac:(body_of (fun s : S.statement_service_delta_implies_scheduled => s Job PStateR schedR j)).
    Definition tgt_service_delta_implies_scheduled : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_delta_implies_scheduled Job d PStateL schedL j)).
    Theorem service_delta_implies_scheduled_correspondence : PropSPropRel src_service_delta_implies_scheduled tgt_service_delta_implies_scheduled.
    Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence;
        [exact (LT _ _ _ _ (SV _ _ Hs j _ _ Ht) (SV _ _ Hs j _ _ (fsv_succ_related _ _ Ht)))|].
      exact (SCT _ _ Hs j _ _ Ht).
    Qed.

    Definition src_service_during_service_at : Prop := ltac:(body_of (fun s : S.statement_service_during_service_at => s Job PStateR schedR j)).
    Definition tgt_service_during_service_at : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_service_at Job d PStateL schedL j)).
    Theorem service_during_service_at_correspondence : PropSPropRel src_service_during_service_at tgt_service_during_service_at.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply fs_iff_correspondence; [exact (fsv_lt0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2))|].
      apply fsv_exists_nat => tR tL Ht.
      apply ar_and_correspondence; [exact (RANGE _ _ _ _ _ _ H1 Ht H2)|].
      exact (fsv_lt0 _ _ (SA _ _ Hs j _ _ Ht)).
    Qed.

    Definition src_cumulative_service_implies_scheduled : Prop := ltac:(body_of (fun s : S.statement_cumulative_service_implies_scheduled => s Job PStateR schedR j)).
    Definition tgt_cumulative_service_implies_scheduled : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_cumulative_service_implies_scheduled Job d PStateL schedL j)).
    Theorem cumulative_service_implies_scheduled_correspondence : PropSPropRel src_cumulative_service_implies_scheduled tgt_cumulative_service_implies_scheduled.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (fsv_lt0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2))|].
      apply fsv_exists_nat => tR tL Ht.
      apply ar_and_correspondence; [exact (RANGE _ _ _ _ _ _ H1 Ht H2)|].
      exact (SCT _ _ Hs j _ _ Ht).
    Qed.

    Definition src_positive_service_implies_scheduled_before : Prop := ltac:(body_of (fun s : S.statement_positive_service_implies_scheduled_before => s Job PStateR schedR j)).
    Definition tgt_positive_service_implies_scheduled_before : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_positive_service_implies_scheduled_before Job d PStateL schedL j)).
    Theorem positive_service_implies_scheduled_before_correspondence : PropSPropRel src_positive_service_implies_scheduled_before tgt_positive_service_implies_scheduled_before.
    Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fsv_lt0 _ _ (SV _ _ Hs j _ _ Ht))|].
      apply fsv_exists_nat => t'R t'L Ht'.
      apply ar_and_correspondence; [exact (LT _ _ _ _ Ht' Ht)|].
      exact (SCT _ _ Hs j _ _ Ht').
    Qed.

    Definition src_service_during_service_at_earliest : Prop := ltac:(body_of (fun s : S.statement_service_during_service_at_earliest => s Job PStateR schedR j)).
    Definition tgt_service_during_service_at_earliest : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_service_at_earliest Job d PStateL schedL j)).
    Theorem service_during_service_at_earliest_correspondence : PropSPropRel src_service_during_service_at_earliest tgt_service_during_service_at_earliest.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (fsv_lt0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2))|].
      apply fsv_exists_nat => tR tL Ht.
      apply ar_and_correspondence; [exact (RANGE _ _ _ _ _ _ H1 Ht H2)|].
      apply ar_and_correspondence; [exact (fsv_lt0 _ _ (SA _ _ Hs j _ _ Ht))|].
      exact (fsv_eq0 _ _ (SD _ _ Hs j _ _ _ _ H1 Ht)).
    Qed.

    Definition src_service_during_scheduled_at_earliest : Prop := ltac:(body_of (fun s : S.statement_service_during_scheduled_at_earliest => s Job PStateR schedR j)).
    Definition tgt_service_during_scheduled_at_earliest : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_during_scheduled_at_earliest Job d PStateL schedL j)).
    Theorem service_during_scheduled_at_earliest_correspondence : PropSPropRel src_service_during_scheduled_at_earliest tgt_service_during_scheduled_at_earliest.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (fsv_lt0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2))|].
      apply fsv_exists_nat => tR tL Ht.
      apply ar_and_correspondence; [exact (RANGE _ _ _ _ _ _ H1 Ht H2)|].
      apply ar_and_correspondence; [exact (SCT _ _ Hs j _ _ Ht)|].
      exact (fsv_eq0 _ _ (SD _ _ Hs j _ _ _ _ H1 Ht)).
    Qed.

    Definition src_no_service_not_scheduled : Prop := ltac:(body_of (fun s : S.statement_no_service_not_scheduled => s Job PStateR schedR j)).
    Definition tgt_no_service_not_scheduled : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_no_service_not_scheduled Job d PStateL schedL j)).
    Theorem no_service_not_scheduled_correspondence : PropSPropRel src_no_service_not_scheduled tgt_no_service_not_scheduled.
    Proof.
      apply ar_imp_correspondence; [exact IDEAL|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply fs_iff_correspondence; [exact (NT _ _ (SCH _ _ Hs j _ _ Ht))|].
      exact (fsv_eq0 _ _ (SA _ _ Hs j _ _ Ht)).
    Qed.

    Definition src_no_service_during_implies_not_scheduled : Prop := ltac:(body_of (fun s : S.statement_no_service_during_implies_not_scheduled => s Job PStateR schedR j)).
    Definition tgt_no_service_during_implies_not_scheduled : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_no_service_during_implies_not_scheduled Job d PStateL schedL j)).
    Theorem no_service_during_implies_not_scheduled_correspondence : PropSPropRel src_no_service_during_implies_not_scheduled tgt_no_service_during_implies_not_scheduled.
    Proof.
      apply ar_imp_correspondence; [exact IDEAL|].
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (fsv_eq0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2))|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (RANGE _ _ _ _ _ _ H1 Ht H2)|].
      exact (NT _ _ (SCH _ _ Hs j _ _ Ht)).
    Qed.

    Definition src_scheduled_implies_cumulative_service : Prop := ltac:(body_of (fun s : S.statement_scheduled_implies_cumulative_service => s Job PStateR schedR j)).
    Definition tgt_scheduled_implies_cumulative_service : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_scheduled_implies_cumulative_service Job d PStateL schedL j)).
    Theorem scheduled_implies_cumulative_service_correspondence : PropSPropRel src_scheduled_implies_cumulative_service tgt_scheduled_implies_cumulative_service.
    Proof.
      apply ar_imp_correspondence; [exact IDEAL|].
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [|exact (fsv_lt0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2))].
      apply fsv_exists_nat => tR tL Ht.
      apply ar_and_correspondence; [exact (RANGE _ _ _ _ _ _ H1 Ht H2)|].
      exact (SCT _ _ Hs j _ _ Ht).
    Qed.

    Definition src_scheduled_implies_nonzero_service : Prop := ltac:(body_of (fun s : S.statement_scheduled_implies_nonzero_service => s Job PStateR schedR j)).
    Definition tgt_scheduled_implies_nonzero_service : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_scheduled_implies_nonzero_service Job d PStateL schedL j)).
    Theorem scheduled_implies_nonzero_service_correspondence : PropSPropRel src_scheduled_implies_nonzero_service tgt_scheduled_implies_nonzero_service.
    Proof.
      apply ar_imp_correspondence; [exact IDEAL|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [|exact (fsv_lt0 _ _ (SV _ _ Hs j _ _ Ht))].
      apply fsv_exists_nat => t'R t'L Ht'.
      apply ar_and_correspondence; [exact (LT _ _ _ _ Ht' Ht)|].
      exact (SCT _ _ Hs j _ _ Ht').
    Qed.

    Definition src_unit_service_at1 : Prop := ltac:(body_of (fun s : S.statement_unit_service_at1 => s Job PStateR schedR j)).
    Definition tgt_unit_service_at1 : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_unit_service_at1 Job d PStateL schedL j)).
    Theorem unit_service_at1_correspondence : PropSPropRel src_unit_service_at1 tgt_unit_service_at1.
    Proof.
      apply ar_imp_correspondence; [exact IDEAL|].
      apply ar_imp_correspondence; [exact UNIT|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (SCT _ _ Hs j _ _ Ht)|].
      exact (EQ _ _ _ _ (SA _ _ Hs j _ _ Ht) (C 1)).
    Qed.

    Section AfterArrival.
      Variable jaR : prosa.behavior.job.JobArrival Job.
      Variable jaL : I.Prosa_Behavior_Job_JobArrival Job d.
      Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
      Let MUST := fs_jobs_must_arrive_related Job PStateR PStateL R schedR schedL Hs jaR jaL Hja.
      Let JA := Hja j.

      Definition src_not_scheduled_before_arrival : Prop := ltac:(body_of (fun s : S.statement_not_scheduled_before_arrival => s Job PStateR schedR j jaR)).
      Definition tgt_not_scheduled_before_arrival : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_not_scheduled_before_arrival Job d PStateL schedL j jaL)).
      Theorem not_scheduled_before_arrival_correspondence : PropSPropRel src_not_scheduled_before_arrival tgt_not_scheduled_before_arrival.
      Proof.
      apply ar_imp_correspondence; [exact MUST|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (LT _ _ _ _ Ht JA)|].
      exact (NT _ _ (SCH _ _ Hs j _ _ Ht)).
    Qed.

      Definition src_positive_service_implies_scheduled_since_arrival : Prop := ltac:(body_of (fun s : S.statement_positive_service_implies_scheduled_since_arrival => s Job PStateR schedR j jaR)).
      Definition tgt_positive_service_implies_scheduled_since_arrival : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_positive_service_implies_scheduled_since_arrival Job d PStateL schedL j jaL)).
      Theorem positive_service_implies_scheduled_since_arrival_correspondence : PropSPropRel src_positive_service_implies_scheduled_since_arrival tgt_positive_service_implies_scheduled_since_arrival.
      Proof.
      apply ar_imp_correspondence; [exact MUST|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fsv_lt0 _ _ (SV _ _ Hs j _ _ Ht))|].
      apply fsv_exists_nat => t'R t'L Ht'.
      apply ar_and_correspondence; [exact (RANGE _ _ _ _ _ _ JA Ht' Ht)|].
      exact (SCT _ _ Hs j _ _ Ht').
    Qed.

      Definition src_service_before_job_arrival_zero : Prop := ltac:(body_of (fun s : S.statement_service_before_job_arrival_zero => s Job PStateR schedR j jaR)).
      Definition tgt_service_before_job_arrival_zero : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_before_job_arrival_zero Job d PStateL schedL j jaL)).
      Theorem service_before_job_arrival_zero_correspondence : PropSPropRel src_service_before_job_arrival_zero tgt_service_before_job_arrival_zero.
      Proof.
      apply ar_imp_correspondence; [exact MUST|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (LT _ _ _ _ Ht JA)|].
      exact (fsv_eq0 _ _ (SA _ _ Hs j _ _ Ht)).
    Qed.

      Definition src_cumulative_service_before_job_arrival_zero : Prop := ltac:(body_of (fun s : S.statement_cumulative_service_before_job_arrival_zero => s Job PStateR schedR j jaR)).
      Definition tgt_cumulative_service_before_job_arrival_zero : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_cumulative_service_before_job_arrival_zero Job d PStateL schedL j jaL)).
      Theorem cumulative_service_before_job_arrival_zero_correspondence : PropSPropRel src_cumulative_service_before_job_arrival_zero tgt_cumulative_service_before_job_arrival_zero.
      Proof.
      apply ar_imp_correspondence; [exact MUST|].
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H2 JA)|].
      exact (fsv_eq0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2)).
    Qed.

      Definition src_ignore_service_before_arrival : Prop := ltac:(body_of (fun s : S.statement_ignore_service_before_arrival => s Job PStateR schedR j jaR)).
      Definition tgt_ignore_service_before_arrival : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_ignore_service_before_arrival Job d PStateL schedL j jaL)).
      Theorem ignore_service_before_arrival_correspondence : PropSPropRel src_ignore_service_before_arrival tgt_ignore_service_before_arrival.
      Proof.
      apply ar_imp_correspondence; [exact MUST|].
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H1 JA)|].
      apply ar_imp_correspondence; [exact (LE _ _ _ _ JA H2)|].
      exact (EQ _ _ _ _ (SD _ _ Hs j _ _ _ _ H1 H2) (SD _ _ Hs j _ _ _ _ JA H2)).
    Qed.

      Definition src_no_service_before_arrival : Prop := ltac:(body_of (fun s : S.statement_no_service_before_arrival => s Job PStateR schedR j jaR)).
      Definition tgt_no_service_before_arrival : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_no_service_before_arrival Job d PStateL schedL j jaL)).
      Theorem no_service_before_arrival_correspondence : PropSPropRel src_no_service_before_arrival tgt_no_service_before_arrival.
      Proof.
      apply ar_imp_correspondence; [exact MUST|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ Ht JA)|].
      exact (fsv_eq0 _ _ (SV _ _ Hs j _ _ Ht)).
    Qed.
    End AfterArrival.

    Definition src_constant_service_implies_no_service_during : Prop := ltac:(body_of (fun s : S.statement_constant_service_implies_no_service_during => s Job PStateR schedR j)).
    Definition tgt_constant_service_implies_no_service_during : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_constant_service_implies_no_service_during Job d PStateL schedL j)).
    Theorem constant_service_implies_no_service_during_correspondence : PropSPropRel src_constant_service_implies_no_service_during tgt_constant_service_implies_no_service_during.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H1 H2)|].
      apply ar_imp_correspondence; [exact (EQ _ _ _ _ (SV _ _ Hs j _ _ H1) (SV _ _ Hs j _ _ H2))|].
      exact (fsv_eq0 _ _ (SD _ _ Hs j _ _ _ _ H1 H2)).
    Qed.

    Definition src_constant_service_implies_not_scheduled : Prop := ltac:(body_of (fun s : S.statement_constant_service_implies_not_scheduled => s Job PStateR schedR j)).
    Definition tgt_constant_service_implies_not_scheduled : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_constant_service_implies_not_scheduled Job d PStateL schedL j)).
    Theorem constant_service_implies_not_scheduled_correspondence : PropSPropRel src_constant_service_implies_not_scheduled tgt_constant_service_implies_not_scheduled.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H1 H2)|].
      apply ar_imp_correspondence; [exact (EQ _ _ _ _ (SV _ _ Hs j _ _ H1) (SV _ _ Hs j _ _ H2))|].
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (RANGE _ _ _ _ _ _ H1 Ht H2)|].
      exact (fsv_eq0 _ _ (SA _ _ Hs j _ _ Ht)).
    Qed.

    Let POS xR xL Hx : ArBoolRel (ltn O (@prosa.behavior.service.service_at Job PStateR schedR j xR))
        (I.Decidable_decide (sub_imported_lt Lean.Nat_zero
            (I.Prosa_Behavior_Service_service_at Job d PStateL schedL j xL))
          (I.Nat_decLt Lean.Nat_zero (I.Prosa_Behavior_Service_service_at Job d PStateL schedL j xL))) :=
      ar_decide_lt_related _ _ _ _ (C O) (SA _ _ Hs j _ _ Hx).

    Definition src_same_service_implies_serviced_at_earlier_times : Prop := ltac:(body_of (fun s : S.statement_same_service_implies_serviced_at_earlier_times => s Job PStateR schedR j)).
    Definition tgt_same_service_implies_serviced_at_earlier_times : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_same_service_implies_serviced_at_earlier_times Job d PStateL schedL j)).
    Theorem same_service_implies_serviced_at_earlier_times_correspondence : PropSPropRel src_same_service_implies_serviced_at_earlier_times tgt_same_service_implies_serviced_at_earlier_times.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H1 H2)|].
      apply ar_imp_correspondence; [exact (EQ _ _ _ _ (SV _ _ Hs j _ _ H1) (SV _ _ Hs j _ _ H2))|].
      exact (fsv_bool_eq_correspondence _ _ _ _
        (fsv_exists_ord_related _ _ _ _ H1 POS) (fsv_exists_ord_related _ _ _ _ H2 POS)).
    Qed.

    Definition src_same_service_implies_scheduled_at_earlier_times : Prop := ltac:(body_of (fun s : S.statement_same_service_implies_scheduled_at_earlier_times => s Job PStateR schedR j)).
    Definition tgt_same_service_implies_scheduled_at_earlier_times : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_same_service_implies_scheduled_at_earlier_times Job d PStateL schedL j)).
    Theorem same_service_implies_scheduled_at_earlier_times_correspondence : PropSPropRel src_same_service_implies_scheduled_at_earlier_times tgt_same_service_implies_scheduled_at_earlier_times.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (LE _ _ _ _ H1 H2)|].
      apply ar_imp_correspondence; [exact (EQ _ _ _ _ (SV _ _ Hs j _ _ H1) (SV _ _ Hs j _ _ H2))|].
      apply ar_imp_correspondence; [exact IDEAL|].
      exact (fsv_bool_eq_correspondence _ _ _ _
        (fsv_exists_ord_related _ _ _ _ H1 (fun xR xL Hx => SCH _ _ Hs j _ _ Hx))
        (fsv_exists_ord_related _ _ _ _ H2 (fun xR xL Hx => SCH _ _ Hs j _ _ Hx))).
    Qed.

    Definition src_kth_scheduling_time : Prop := ltac:(body_of (fun s : S.statement_kth_scheduling_time => s Job PStateR schedR j)).
    Definition tgt_kth_scheduling_time : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_kth_scheduling_time Job d PStateL schedL j)).
    Theorem kth_scheduling_time_correspondence : PropSPropRel src_kth_scheduling_time tgt_kth_scheduling_time.
    Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_forall_nat_correspondence => t'R t'L Ht'.
      apply ar_forall_nat_correspondence => kR kL Hk.
      apply ar_imp_correspondence; [exact (EQ _ _ _ _ (SV _ _ Hs j _ _ Ht) Hk)|].
      apply ar_imp_correspondence; [exact (LT _ _ _ _ Hk (SV _ _ Hs j _ _ Ht'))|].
      apply fsv_exists_nat => sR sL Hst.
      apply ar_and_correspondence; [exact (RANGE _ _ _ _ _ _ Ht Hst Ht')|].
      apply ar_and_correspondence; [exact (EQ _ _ _ _ (SV _ _ Hs j _ _ Hst) Hk)|].
      exact (SCT _ _ Hs j _ _ Hst).
    Qed.
  End SchedJob.

  (** *** State-level observation (input: job) *)
  Section StateJob.
  Variable j : Job.
  Definition src_service_in_implies_scheduled_in : Prop := ltac:(body_of (fun s : S.statement_service_in_implies_scheduled_in => s Job PStateR j)).
  Definition tgt_service_in_implies_scheduled_in : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_service_in_implies_scheduled_in Job d PStateL j)).
  Theorem service_in_implies_scheduled_in_correspondence : PropSPropRel src_service_in_implies_scheduled_in tgt_service_in_implies_scheduled_in.
  Proof.
    apply (fs_forall_state Job PStateR PStateL R) => sR sL Hst.
    apply ar_imp_correspondence;
      [exact (NT _ _ (svc_scheduled_in_related Job PStateR PStateL R j _ _ Hst))|].
    exact (fsv_eq0 _ _ (fsv_service_in_state Job PStateR PStateL R j _ _ Hst)).
  Qed.
  End StateJob.

  (** *** Generic processor (inputs: job arrival, arrival sequence) *)
  Section Generic.
    Variable jaR : prosa.behavior.job.JobArrival Job.
    Variable jaL : I.Prosa_Behavior_Job_JobArrival Job d.
    Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job d.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
    Let VA := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
    Let JCF sR sL Hs := fs_jobs_come_from_related Job PStateR PStateL R sR sL Hs arrR arrL Harr.
    Let JMA sR sL Hs := fs_jobs_must_arrive_related Job PStateR PStateL R sR sL Hs jaR jaL Hja.

    Definition src_receives_service_and_served_at_consistent : Prop := ltac:(body_of (fun s : S.statement_receives_service_and_served_at_consistent => s Job jaR PStateR arrR)).
    Definition tgt_receives_service_and_served_at_consistent : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_receives_service_and_served_at_consistent Job d jaL PStateL arrL)).
    Theorem receives_service_and_served_at_consistent_correspondence : PropSPropRel src_receives_service_and_served_at_consistent tgt_receives_service_and_served_at_consistent.
    Proof.
      apply ar_imp_correspondence; [exact VA|].
      apply FS => sR sL Hs.
      apply ar_imp_correspondence; [exact (JCF _ _ Hs)|].
      apply ar_imp_correspondence; [exact (JMA _ _ Hs)|].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (TR _ _ (RCV _ _ Hs j _ _ Ht))|].
      exact (TR _ _ (ar_decide_mem_related Job j _ _
        (fs_served_jobs_at_related Job PStateR PStateL R sR sL Hs arrR arrL Harr _ _ Ht))).
    Qed.

    Definition src_no_service_received_when_idle : Prop := ltac:(body_of (fun s : S.statement_no_service_received_when_idle => s Job jaR PStateR arrR)).
    Definition tgt_no_service_received_when_idle : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_no_service_received_when_idle Job d jaL PStateL arrL)).
    Theorem no_service_received_when_idle_correspondence : PropSPropRel src_no_service_received_when_idle tgt_no_service_received_when_idle.
    Proof.
      apply ar_imp_correspondence; [exact VA|].
      apply FS => sR sL Hs.
      apply ar_imp_correspondence; [exact (JCF _ _ Hs)|].
      apply ar_imp_correspondence; [exact (JMA _ _ Hs)|].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence;
        [exact (TR _ _ (fs_is_idle_related Job PStateR PStateL R sR sL Hs arrR arrL Harr _ _ Ht))|].
      exact (NT _ _ (RCV _ _ Hs j _ _ Ht)).
    Qed.

    Section Served.
      Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
      Variable schedL : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
      Hypothesis Hs : SR schedR schedL.
      Variable j : Job.
      Definition src_served_at_and_receives_service_consistent : Prop := ltac:(body_of (fun s : S.statement_served_at_and_receives_service_consistent => s Job PStateR arrR schedR j)).
      Definition tgt_served_at_and_receives_service_consistent : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_served_at_and_receives_service_consistent Job d PStateL arrL schedL j)).
      Theorem served_at_and_receives_service_consistent_correspondence : PropSPropRel src_served_at_and_receives_service_consistent tgt_served_at_and_receives_service_consistent.
      Proof.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence;
        [exact (TR _ _ (ar_decide_mem_related Job j _ _
          (fs_served_jobs_at_related Job PStateR PStateL R schedR schedL Hs arrR arrL Harr _ _ Ht)))|].
      exact (TR _ _ (RCV _ _ Hs j _ _ Ht)).
    Qed.
    End Served.
  End Generic.

  (** *** Uniprocessor and incremental service *)
  Definition src_only_one_job_receives_service_at_uni : Prop := ltac:(body_of (fun s : S.statement_only_one_job_receives_service_at_uni => s Job PStateR)).
  Definition tgt_only_one_job_receives_service_at_uni : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_only_one_job_receives_service_at_uni Job d PStateL)).
  Theorem only_one_job_receives_service_at_uni_correspondence : PropSPropRel src_only_one_job_receives_service_at_uni tgt_only_one_job_receives_service_at_uni.
  Proof.
    apply ar_imp_correspondence; [exact (fs_uniprocessor_related Job PStateR PStateL R)|].
    apply FS => sR sL Hs.
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (TR _ _ (RCV _ _ Hs j1 _ _ Ht))|].
    apply ar_imp_correspondence; [exact (TR _ _ (RCV _ _ Hs j2 _ _ Ht))|].
    exact (fs_eq_id_correspondence Job j1 j2).
  Qed.

  Section Incremental.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
    Hypothesis Hs : SR schedR schedL.
    Definition src_incremental_service_during : Prop := ltac:(body_of (fun s : S.statement_incremental_service_during => s Job PStateR schedR)).
    Definition tgt_incremental_service_during : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_incremental_service_during Job d PStateL schedL)).
    Theorem incremental_service_during_correspondence : PropSPropRel src_incremental_service_during tgt_incremental_service_during.
    Proof.
      apply ar_imp_correspondence; [exact UNIT|].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_forall_nat_correspondence => kR kL Hk.
      apply ar_imp_correspondence; [exact (LT _ _ _ _ Hk (SD _ _ Hs j _ _ _ _ H1 H2))|].
      apply fsv_exists_nat => tR tL Ht.
      apply ar_and_correspondence; [exact (fsv_range_le_lt _ _ _ _ _ _ H1 Ht H2)|].
      apply ar_and_correspondence; [exact (SCT _ _ Hs j _ _ Ht)|].
      exact (EQ _ _ _ _ (SD _ _ Hs j _ _ _ _ H1 Ht) Hk).
    Qed.
  End Incremental.

  (** *** Two schedules (inputs: both schedules) *)
  Section TwoSchedules.
    Variable s1R : @prosa.behavior.schedule.schedule Job PStateR.
    Variable s1L : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
    Hypothesis Hs1 : SR s1R s1L.
    Variable s2R : @prosa.behavior.schedule.schedule Job PStateR.
    Variable s2L : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
    Hypothesis Hs2 : SR s2R s2L.

    Definition src_same_service_during : Prop := ltac:(body_of (fun s : S.statement_same_service_during => s Job PStateR s1R s2R)).
    Definition tgt_same_service_during : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_same_service_during Job d PStateL s1L s2L)).
    Theorem same_service_during_correspondence : PropSPropRel src_same_service_during tgt_same_service_during.
    Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_forall_identity_correspondence => j.
      apply ar_imp_correspondence.
      - apply ar_forall_nat_correspondence => tR tL Ht.
        apply ar_imp_correspondence; [exact (fsv_range_le_lt _ _ _ _ _ _ H1 Ht H2)|].
        exact (EQ _ _ _ _ (SA _ _ Hs1 j _ _ Ht) (SA _ _ Hs2 j _ _ Ht)).
      - exact (EQ _ _ _ _ (SD _ _ Hs1 j _ _ _ _ H1 H2) (SD _ _ Hs2 j _ _ _ _ H1 H2)).
    Qed.

    Section Graph.
      Hypothesis Hgraph : FsvStateGraph Job PStateR PStateL R.
      Definition src_equal_prefix_implies_same_service_during : Prop := ltac:(body_of (fun s : S.statement_equal_prefix_implies_same_service_during => s Job PStateR s1R s2R)).
      Definition tgt_equal_prefix_implies_same_service_during : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_equal_prefix_implies_same_service_during Job d PStateL s1L s2L)).
      Theorem equal_prefix_implies_same_service_during_correspondence : PropSPropRel src_equal_prefix_implies_same_service_during tgt_equal_prefix_implies_same_service_during.
      Proof.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence.
      - apply ar_forall_nat_correspondence => tR tL Ht.
        apply ar_imp_correspondence; [exact (fsv_range_le_lt _ _ _ _ _ _ H1 Ht H2)|].
        exact (fsv_state_eq_correspondence Job PStateR PStateL R Hgraph _ _ _ _ (Hs1 _ _ Ht) (Hs2 _ _ Ht)).
      - apply ar_forall_identity_correspondence => j.
        exact (EQ _ _ _ _ (SD _ _ Hs1 j _ _ _ _ H1 H2) (SD _ _ Hs2 j _ _ _ _ H1 H2)).
    Qed.

      Definition src_identical_prefix_service : Prop := ltac:(body_of (fun s : S.statement_identical_prefix_service => s Job PStateR s1R s2R)).
      Definition tgt_identical_prefix_service : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Service_identical_prefix_service Job d PStateL s1L s2L)).
      Theorem identical_prefix_service_correspondence : PropSPropRel src_identical_prefix_service tgt_identical_prefix_service.
      Proof.
      apply ar_forall_nat_correspondence => hR hL Hh.
      apply ar_imp_correspondence.
      - unfold prosa.analysis.definitions.schedule_prefix.identical_prefix.
        cbn [I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix].
        apply ar_forall_nat_correspondence => tR tL Ht.
        apply ar_imp_correspondence; [exact (LT _ _ _ _ Ht Hh)|].
        exact (fsv_state_eq_correspondence Job PStateR PStateL R Hgraph _ _ _ _ (Hs1 _ _ Ht) (Hs2 _ _ Ht)).
      - apply ar_forall_identity_correspondence => j.
        exact (EQ _ _ _ _ (SV _ _ Hs1 j _ _ Hh) (SV _ _ Hs2 j _ _ Hh)).
    Qed.
    End Graph.
  End TwoSchedules.
End Statements.
