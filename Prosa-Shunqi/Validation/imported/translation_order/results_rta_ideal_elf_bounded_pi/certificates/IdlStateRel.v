From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import behavior.all model.processor.ideal.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaIdealElfBoundedPi ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence
  IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlServiceScheduleOperations
  IdlSupplyScheduleBaseAdapter IdlSupplyScheduleOperations.

Module I := ImportedRtaIdealElfBoundedPi.
Module SSO := FoundationCertificates.IdlServiceScheduleOperations.
Module SUP := FoundationCertificates.IdlSupplyScheduleOperations.

(** The ideal uniprocessor states related constructor-wise (the Option map); the unit core; [scheduled_on] and
    [service_on] per core by the state comparison; the core enumeration of the Lean model is the singleton list,
    from its accepted duplicate-freedom and completeness theorems. *)

Section IdlState.
  Context (Job : eqType).
  Let dJ := svc_decidable_eq Job.
  Let PR := prosa.model.processor.ideal.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let CL := I.Prosa_Behavior_Schedule_ProcessorState_Core_inst2 Job dJ PL.

  Local Transparent prosa.behavior.schedule.scheduled_on prosa.behavior.schedule.service_on
    prosa.behavior.schedule.supply_on.

  Definition idl_st_to (s : option Job) : I.Option Job :=
    match s with
    | None => I.Option_none Job
    | Some j => I.Option_some Job j
    end.

  Definition idl_st_from (s : I.Option Job) : option Job :=
    match s with
    | I.Option_none => None
    | I.Option_some j => Some j
    end.

  Lemma idl_st_rt_source s : Logic.eq (idl_st_from (idl_st_to s)) s.
  Proof. by case: s. Qed.
  Lemma idl_st_rt_target s : Lean.eq (idl_st_to (idl_st_from s)) s.
  Proof. destruct s; exact (@Lean.eq_refl _ _). Qed.

  Definition IdlStateRelation (sR : option Job) (sL : I.Option Job) : SProp := Lean.eq (idl_st_to sR) sL.

  Let CR := @prosa.behavior.schedule.Core Job PR.
  Definition idl_co_to (c : CR) : CL := I.PUnit_unit.
  Definition idl_co_from (c : CL) : CR := tt.
  Lemma idl_co_rt_source c : Logic.eq (idl_co_from (idl_co_to c)) c.
  Proof. by case: c. Qed.
  Lemma idl_co_rt_target c : Lean.eq (idl_co_to (idl_co_from c)) c.
  Proof. destruct c; exact (@Lean.eq_refl _ _). Qed.

  (** The Lean core enumeration is the singleton list: it is complete and duplicate-free (the accepted interface
      theorems), and the core type has a single element.  (Lean lists over the unit core live at the list universe
      instance [List_inst1] of this export.) *)

  Let enumL := I.Prosa_Validation_ScheduleInterface_coreEnumeration_inst4 Job dJ PL.
  Let one := I.List_cons_inst1 CL I.PUnit_unit (I.List_nil_inst1 CL).

  Lemma idl_mem_nil (u : CL) (G : SProp) : I.List_Mem_inst1 CL u (I.List_nil_inst1 CL) -> G.
  Proof.
    intro H.
    exact (match H in I.List_Mem_inst1 _ _ l return
             (match l with I.List_nil_inst1 => G | I.List_cons_inst1 _ _ => I.True end) with
           | I.List_Mem_head_inst1 _ => I.True_intro
           | I.List_Mem_tail_inst1 _ _ _ => I.True_intro end).
  Qed.

  Lemma idl_pairwise_head (x y : CL) (t : I.List_inst1 CL) (G : SProp) :
    I.List_Nodup_inst1 CL (I.List_cons_inst1 CL x (I.List_cons_inst1 CL y t)) -> G.
  Proof.
    intro N. unfold I.List_Nodup_inst1 in N.
    refine (match N in I.List_Pairwise_inst1 _ _ l return
             (match l with
              | I.List_cons_inst1 _ (I.List_cons_inst1 _ _) => G
              | _ => I.True end) with
           | I.List_Pairwise_nil_inst1 => I.True_intro
           | I.List_Pairwise_cons_inst1 a l H _ => _ end).
    destruct l as [|b l']; [exact I.True_intro|].
    have Hab := H b (I.List_Mem_head_inst1 CL b l').
    destruct a, b. destruct (Hab (@Lean.eq_refl _ _)).
  Qed.

  Lemma idl_enum_singleton : Lean.eq one enumL.
  Proof.
    have C := I.Prosa_Validation_ScheduleInterface_coreEnumeration_complete_inst2 Job dJ PL I.PUnit_unit.
    have N := I.Prosa_Validation_ScheduleInterface_coreEnumeration_nodup_inst1 Job dJ PL.
    unfold one. fold enumL in C, N |- *. revert C N. generalize enumL as l. intros l C N.
    destruct l as [|x [|y t]].
    - exact (idl_mem_nil _ _ C).
    - destruct x. exact (@Lean.eq_refl _ _).
    - exact (idl_pairwise_head _ _ _ _ N).
  Qed.

  Lemma idl_core_enumeration_rel :
    SSO.SvcCoreEnumerationRel CR CL idl_co_to enumL.
  Proof.
    unfold SSO.SvcCoreEnumerationRel.
    have E : Logic.eq (map idl_co_to (enum CR)) [:: I.PUnit_unit].
    { by rewrite enumT unlock. }
    rewrite E. exact idl_enum_singleton.
  Qed.

  (** Per-core observations. *)

  Lemma idl_option_some_eq (s : option Job) (j : Job) :
    PropSPropRel (is_true (s == Some j)) (Lean.eq (idl_st_to s) (I.Option_some Job j)).
  Proof.
    apply prop_sprop_rel_intro.
    - intro H. move/eqP: H => ->. exact (@Lean.eq_refl _ _).
    - intro H. apply strictly_inhabits.
      have Hcoq := imported_eq_to_coq_eq _ _ H.
      destruct s as [k|]; cbn in Hcoq.
      + injection Hcoq as Hkj. subst k. exact (eqxx (Some j)).
      + discriminate Hcoq.
  Qed.

  Lemma idl_scheduled_on_rel (j : Job) (sR : option Job) (sL : I.Option Job) (cR : CR) :
    IdlStateRelation sR sL ->
    SvcBoolRel (@prosa.behavior.schedule.scheduled_on Job PR j sR cR)
      (SSO.svc_target_scheduled_on Job PL j sL (idl_co_to cR)).
  Proof.
    intro Hs. have E := imported_eq_to_coq_eq _ _ Hs. rewrite <- E.
    cbn. apply ar_decide_bool_correspondence. exact (idl_option_some_eq sR j).
  Qed.

  Lemma idl_decide_state_related (j : Job) (sR : option Job) d :
    SvcBoolRel (sR == Some j) (I.Decidable_decide (Lean.eq (idl_st_to sR) (I.Option_some Job j)) d).
  Proof. apply ar_decide_bool_correspondence. exact (idl_option_some_eq sR j). Qed.

  Lemma idl_service_on_rel (j : Job) (sR : option Job) (sL : I.Option Job) (cR : CR) :
    IdlStateRelation sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_on Job PR j sR cR)
      (SSO.svc_target_service_on Job PL j sL (idl_co_to cR)).
  Proof.
    intro Hs. have E := imported_eq_to_coq_eq _ _ Hs. rewrite <- E. cbn.
    have Hb := idl_decide_state_related j sR
      (I.Option_instDecidableEq Job dJ (idl_st_to sR) (I.Option_some Job j)).
    unfold SvcBoolRel in Hb. revert Hb.
    generalize (I.Decidable_decide (Lean.eq (idl_st_to sR) (I.Option_some Job j))
      (I.Option_instDecidableEq Job dJ (idl_st_to sR) (I.Option_some Job j))).
    intros bL Hb. destruct Hb.
    change (opt_eq sR (Some j)) with (sR == Some j).
    destruct (sR == Some j); cbn;
      [exact (sub_nat_rel_canonical 1) | exact (sub_nat_rel_canonical O)].
  Qed.

  Definition idl_psrel : SSO.SvcProcessorStateRel Job PR PL :=
    SSO.Build_SvcProcessorStateRel Job PR PL IdlStateRelation idl_st_to idl_st_from idl_co_to idl_co_from
      idl_st_rt_source idl_st_rt_target idl_co_rt_source idl_co_rt_target
      (fun s => @Lean.eq_refl _ _) idl_st_rt_target
      idl_core_enumeration_rel idl_scheduled_on_rel idl_service_on_rel.

  Lemma idl_supply_on (sR : option Job) (sL : I.Option Job) (cR : CR) :
    SSO.svc_ps_state_rel Job PR PL idl_psrel sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_on Job PR sR cR)
      (SUP.supply_target_supply_on Job PL sL (SSO.svc_ps_core_to_target Job PR PL idl_psrel cR)).
  Proof. intros _. exact (sub_nat_rel_canonical 1). Qed.
End IdlState.
