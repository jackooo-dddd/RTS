(* Two-way processor-state cover for the restricted-supply relation family (developed for the
   ARM/PRM response-time files, whose statements quantify the processor model inside). *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require ImportedRtaArmEdfFullyPreemptive.
From FoundationImported Require Import ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ServiceBaseAdapter ServiceScheduleOperations.
From FoundationCertificates Require SupplyScheduleOperations.

Module I := ImportedRtaArmEdfFullyPreemptive.
Module SUP := FoundationCertificates.SupplyScheduleOperations.

(** Two-way cover of processor models quantified inside a statement, in the
    restricted-supply (service-schedule) relation family: every Rocq model is
    related to a Lean model and conversely, by an [SvcProcessorStateRel]
    together with the pointwise [supply_on] relation. *)

Lemma rsc_ar_svc_list_eq {T : Type} (xs : seq T) :
  Lean.eq (ar_list_to_imported xs) (svc_list_to_imported xs).
Proof.
  induction xs as [|x xs IH]; cbn; [exact (@Lean.eq_refl _ _)|].
  destruct IH. exact (@Lean.eq_refl _ _).
Qed.

Lemma rsc_lean_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma rsc_forall_cover_type (A B : Type) (Rel : A -> B -> Type)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma rsc_map_index_nth (T : eqType) (s t : seq T) :
  uniq s -> size s = size t -> map (fun c => seq.nth c t (seq.index c s)) s = t.
Proof.
  case: s => [|x0 s'] Us Hsz; first by case: t Hsz.
  apply: (@eq_from_nth _ x0); first by rewrite size_map.
  move=> i; rewrite size_map => Hi.
  rewrite (nth_map x0) // (index_uniq x0 Hi Us).
  apply: set_nth_default. by rewrite -Hsz.
Qed.

Section RsCover.
  Context (Job : eqType).
  Let dJ := svc_decidable_eq Job.
  Let PSL := I.Prosa_Behavior_Schedule_ProcessorState Job dJ.

  Definition RsSupplyOnRel (PR : prosa.behavior.schedule.ProcessorState Job) (PL : PSL)
      (R : SvcProcessorStateRel Job PR PL) : SProp :=
    forall sR sL cR, svc_ps_state_rel Job PR PL R sR sL ->
      SubNatRel (@prosa.behavior.schedule.supply_on Job PR sR cR)
        (SUP.supply_target_supply_on Job PL sL (svc_ps_core_to_target Job PR PL R cR)).

  Record RsPSPair (PR : prosa.behavior.schedule.ProcessorState Job) (PL : PSL) : Type := {
    rs_rel : SvcProcessorStateRel Job PR PL;
    rs_sup : RsSupplyOnRel PR PL rs_rel }.

  (** *** Lean model to Rocq model *)

  Section ToSource.
    Variable PL : PSL.
    Let CL := I.Prosa_Behavior_Schedule_ProcessorState_Core Job dJ PL.
    Let SL := I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PL.
    Let decL := I.Prosa_Behavior_Schedule_ProcessorState_coreDecidableEq Job dJ PL.
    Let enumL := I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL.

    Definition rsc_core_eqb (x y : CL) : bool :=
      svc_bool_to_rocq (I.Decidable_decide (Lean.eq x y) (decL x y)).

    Lemma rsc_core_eqP : Equality.axiom rsc_core_eqb.
    Proof.
      intros x y. unfold rsc_core_eqb.
      destruct (decL x y) as [Hne | He]; cbn.
      - apply ReflectF. intro E. destruct E.
        exact (match Hne (@Lean.eq_refl _ x) with end).
      - apply ReflectT. exact (imported_eq_to_coq_eq _ _ He).
    Qed.

    Definition rsc_core_eqType : eqType := HB.pack CL (hasDecEq.Build CL rsc_core_eqP).

    Definition rsc_core_list : seq rsc_core_eqType := ar_list_to_rocq enumL.

    Lemma rsc_core_list_rel : ArListRel rsc_core_list enumL.
    Proof. exact (ar_list_target_roundtrip _). Qed.

    Lemma rsc_core_list_uniq : uniq rsc_core_list.
    Proof.
      exact (sprop_to_prop _ _ (ar_uniq_correspondence rsc_core_eqType _ _ rsc_core_list_rel)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration_nodup Job dJ PL)).
    Qed.

    Lemma rsc_core_list_complete (c : CL) : (c : rsc_core_eqType) \in rsc_core_list.
    Proof.
      exact (sprop_to_prop _ _ (ar_membership_correspondence rsc_core_eqType c _ _ rsc_core_list_rel)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration_complete Job dJ PL c)).
    Qed.

    Definition rsc_core_finType : finType := adhoc_seq_sub_finType rsc_core_list.

    Definition rsc_core_from (c : CL) : rsc_core_finType :=
      @SeqSub rsc_core_eqType rsc_core_list c (rsc_core_list_complete c).

    Lemma rsc_core_enum_map :
      map (@ssval rsc_core_eqType rsc_core_list) (enum rsc_core_finType) = rsc_core_list.
    Proof. rewrite enumT unlock /=. exact (val_seq_sub_enum rsc_core_list_uniq). Qed.

    Definition rsc_src_scheduled_on (j : Job) (s : SL) (c : rsc_core_finType) : bool :=
      svc_bool_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_on Job dJ PL j s (ssval c)).
    Definition rsc_src_supply_on (s : SL) (c : rsc_core_finType) : nat :=
      sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PL s (ssval c)).
    Definition rsc_src_service_on (j : Job) (s : SL) (c : rsc_core_finType) : nat :=
      sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_service_on Job dJ PL j s (ssval c)).

    Lemma rsc_src_law_le j s r : leq (rsc_src_service_on j s r) (rsc_src_supply_on s r).
    Proof.
      exact (sprop_to_prop _ _ (sub_nat_le_correspondence _ _ _ _
        (sub_nat_rel_surjective _) (sub_nat_rel_surjective _))
        (I.service_on_le_supply_on Job dJ PL j s (ssval r))).
    Qed.

    Lemma rsc_bool_false_of_rocq (b : I.Bool) : ~~ svc_bool_to_rocq b -> Lean.eq b I.Bool_false.
    Proof. destruct b; cbn; [intros _; exact (@Lean.eq_refl _ _)|discriminate]. Qed.

    Lemma rsc_src_law_zero j s r : ~~ rsc_src_scheduled_on j s r -> rsc_src_service_on j s r = O.
    Proof.
      unfold rsc_src_scheduled_on, rsc_src_service_on. intro H.
      have E : sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_service_on Job dJ PL j s (ssval r))
          = sub_nat_to_rocq (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)) :=
        f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _
          (I.service_on_implies_scheduled_on Job dJ PL j s (ssval r) (rsc_bool_false_of_rocq _ H))).
      rewrite E. exact (sub_nat_rocq_roundtrip O).
    Qed.

    Definition rsc_ps_to_source : prosa.behavior.schedule.ProcessorState Job :=
      @prosa.behavior.schedule.Build_ProcessorState Job SL rsc_core_finType
        rsc_src_scheduled_on rsc_src_supply_on rsc_src_service_on
        rsc_src_law_le rsc_src_law_zero.

    Lemma rsc_src_core_source_roundtrip (c : rsc_core_finType) : rsc_core_from (ssval c) = c.
    Proof. apply: val_inj. reflexivity. Qed.

    Lemma rsc_src_enumeration_rel :
      SvcCoreEnumerationRel rsc_core_finType CL (@ssval rsc_core_eqType rsc_core_list) enumL.
    Proof.
      unfold SvcCoreEnumerationRel. rewrite rsc_core_enum_map.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (rsc_ar_svc_list_eq _)) rsc_core_list_rel).
    Qed.

    Lemma rsc_src_scheduled_rel (j : Job) (sR sL : SL) (c : rsc_core_finType) :
      Lean.eq sR sL ->
      SvcBoolRel (rsc_src_scheduled_on j sR c) (svc_target_scheduled_on Job PL j sL (ssval c)).
    Proof. intro Hs. destruct Hs. exact (svc_bool_target_roundtrip _). Qed.

    Lemma rsc_src_service_rel (j : Job) (sR sL : SL) (c : rsc_core_finType) :
      Lean.eq sR sL ->
      SubNatRel (rsc_src_service_on j sR c) (svc_target_service_on Job PL j sL (ssval c)).
    Proof. intro Hs. destruct Hs. exact (sub_nat_rel_surjective _). Qed.

    Definition rsc_rel_to_source : SvcProcessorStateRel Job rsc_ps_to_source PL :=
      @Build_SvcProcessorStateRel Job rsc_ps_to_source PL
        (fun sR sL => Lean.eq sR sL) (fun s => s) (fun s => s)
        (fun c => ssval c) rsc_core_from
        (fun s => Logic.eq_refl s) (fun s => @Lean.eq_refl _ s)
        rsc_src_core_source_roundtrip (fun c => @Lean.eq_refl _ c)
        (fun s => @Lean.eq_refl _ s) (fun s => @Lean.eq_refl _ s)
        rsc_src_enumeration_rel
        rsc_src_scheduled_rel rsc_src_service_rel.

    Lemma rsc_sup_to_source : RsSupplyOnRel rsc_ps_to_source PL rsc_rel_to_source.
    Proof.
      intros sR sL c Hs. cbn in Hs. destruct Hs. exact (sub_nat_rel_surjective _).
    Qed.

    Definition rsc_pair_to_source : RsPSPair rsc_ps_to_source PL :=
      {| rs_rel := rsc_rel_to_source; rs_sup := rsc_sup_to_source |}.
  End ToSource.
  (** *** Rocq model to Lean model

      The Lean model is built over the Rocq state and core types, with the
      [Fintype] of the Rocq enumeration.  Its [coreEnumeration] is a
      permutation [l] of that enumeration (by the interface theorems), so the
      core map is the bijection [rsc_sigma] sending the [i]-th enumerated core
      to the [i]-th element of [l]; the Lean per-core fields are the Rocq ones
      read through its inverse. *)

  Section ToTarget.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Let CR := @prosa.behavior.schedule.Core Job PR.
    Let SR := @prosa.behavior.schedule.State Job PR.
    Let enumR : seq CR := enum CR.
    Let enumL0 : I.List CR := svc_list_to_imported enumR.

    Lemma rsc_enum_nodup : I.List_Nodup CR enumL0.
    Proof.
      refine (rsc_lean_transport (fun l => I.List_Nodup CR l) _ _ (rsc_ar_svc_list_eq enumR) _).
      exact (prop_to_sprop _ _ (ar_uniq_correspondence CR enumR _ (@Lean.eq_refl _ (ar_list_to_imported enumR)))
        (enum_uniq CR)).
    Qed.

    Lemma rsc_enum_complete : forall c : CR, ar_target_mem c enumL0.
    Proof.
      intro c.
      refine (rsc_lean_transport (fun l => ar_target_mem c l) _ _ (rsc_ar_svc_list_eq enumR) _).
      exact (prop_to_sprop _ _ (ar_membership_correspondence CR c enumR _ (@Lean.eq_refl _ (ar_list_to_imported enumR)))
        (mem_enum CR c)).
    Qed.

    Let F := I.Prosa_Validation_ProcessorStateCoverInterface_fintypeOfNodupListing CR enumL0
      rsc_enum_nodup rsc_enum_complete.

    Lemma rsc_law_le_at (g : CR -> CR) : forall j s r,
      I.LE_le_inst1 I.Prosa_Behavior_Job_work I.instLENat
        (sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s (g r)))
        (sub_nat_to_imported (@prosa.behavior.schedule.supply_on Job PR s (g r))).
    Proof.
      intros j s r.
      exact (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _
        (sub_nat_rel_canonical _) (sub_nat_rel_canonical _))
        (@prosa.behavior.schedule.service_on_le_supply_on Job PR j s (g r))).
    Qed.

    Lemma rsc_law_zero_at (g : CR -> CR) : forall j s r,
      Lean.eq (svc_bool_to_imported (@prosa.behavior.schedule.scheduled_on Job PR j s (g r))) I.Bool_false ->
      Lean.eq (sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s (g r)))
        (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)).
    Proof.
      intros j s r H.
      destruct (@prosa.behavior.schedule.scheduled_on Job PR j s (g r)) eqn:E.
      - exact (svc_false_elim _ (svc_false_ne_true (sub_imported_eq_sym _ _ H))).
      - have Z := @prosa.behavior.schedule.service_on_implies_scheduled_on Job PR j s (g r) (negbT E).
        exact (rsc_lean_transport (fun n => Lean.eq (sub_nat_to_imported n)
            (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)))
          _ _ (coq_eq_to_imported_eq _ _ (Logic.eq_sym Z)) (sub_nat_rel_canonical O)).
    Qed.

    (** The Lean model with per-core fields read through [g]. *)
    Definition rsc_ps_at (g : CR -> CR) : PSL :=
      I.Prosa_Behavior_Schedule_ProcessorState_mk Job dJ SR CR F (svc_decidable_eq CR)
        (fun j s c => svc_bool_to_imported (@prosa.behavior.schedule.scheduled_on Job PR j s (g c)))
        (fun s c => sub_nat_to_imported (@prosa.behavior.schedule.supply_on Job PR s (g c)))
        (fun j s c => sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s (g c)))
        (rsc_law_le_at g) (rsc_law_zero_at g).

    (** Its core enumeration does not depend on the fields. *)
    Let l : I.List CR := I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ (rsc_ps_at (fun c : CR => c)).
    Let lR : seq CR := ar_list_to_rocq l.

    Lemma rsc_l_rel : ArListRel lR l.
    Proof. exact (ar_list_target_roundtrip _). Qed.

    Lemma rsc_l_uniq : uniq lR.
    Proof.
      exact (sprop_to_prop _ _ (ar_uniq_correspondence CR _ _ rsc_l_rel)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration_nodup Job dJ (rsc_ps_at (fun c : CR => c)))).
    Qed.

    Lemma rsc_l_complete (c : CR) : c \in lR.
    Proof.
      exact (sprop_to_prop _ _ (ar_membership_correspondence CR c _ _ rsc_l_rel)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration_complete Job dJ (rsc_ps_at (fun c : CR => c)) c)).
    Qed.

    Lemma rsc_l_perm : perm_eq lR enumR.
    Proof.
      apply: uniq_perm; [exact rsc_l_uniq|exact (enum_uniq CR)|].
      intro c. by rewrite rsc_l_complete mem_enum.
    Qed.

    Lemma rsc_l_size : size lR = size enumR.
    Proof. exact (perm_size rsc_l_perm). Qed.

    Definition rsc_sigma (c : CR) : CR := seq.nth c lR (seq.index c enumR).
    Definition rsc_sigma_inv (c : CR) : CR := seq.nth c enumR (seq.index c lR).

    Lemma rsc_sigma_inv_sigma (c : CR) : rsc_sigma_inv (rsc_sigma c) = c.
    Proof.
      rewrite /rsc_sigma_inv /rsc_sigma.
      have Hi : (seq.index c enumR < size lR)%N by rewrite rsc_l_size index_mem mem_enum.
      rewrite (index_uniq _ Hi rsc_l_uniq).
      by apply: nth_index; rewrite mem_enum.
    Qed.

    Lemma rsc_sigma_sigma_inv (c : CR) : rsc_sigma (rsc_sigma_inv c) = c.
    Proof.
      rewrite /rsc_sigma_inv /rsc_sigma.
      have Hi : (seq.index c lR < size enumR)%N by rewrite -rsc_l_size index_mem rsc_l_complete.
      rewrite (index_uniq _ Hi (enum_uniq CR)).
      exact: nth_index (rsc_l_complete c).
    Qed.

    Lemma rsc_map_sigma : map rsc_sigma enumR = lR.
    Proof. exact (@rsc_map_index_nth CR enumR lR (enum_uniq CR) (Logic.eq_sym rsc_l_size)). Qed.

    Definition rsc_ps_to_target : PSL := rsc_ps_at rsc_sigma_inv.

    Lemma rsc_enumeration_rel :
      SvcCoreEnumerationRel CR CR rsc_sigma
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ rsc_ps_to_target).
    Proof.
      unfold SvcCoreEnumerationRel. rewrite rsc_map_sigma.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (rsc_ar_svc_list_eq lR)) rsc_l_rel).
    Qed.

    Lemma rsc_tgt_scheduled_rel (j : Job) (sR sL : SR) (c : CR) :
      Lean.eq sR sL ->
      SvcBoolRel (@prosa.behavior.schedule.scheduled_on Job PR j sR c)
        (svc_target_scheduled_on Job rsc_ps_to_target j sL (rsc_sigma c)).
    Proof.
      intro Hs. destruct Hs. unfold SvcBoolRel, svc_target_scheduled_on. cbn.
      rewrite rsc_sigma_inv_sigma. exact (@Lean.eq_refl _ _).
    Qed.

    Lemma rsc_tgt_service_rel (j : Job) (sR sL : SR) (c : CR) :
      Lean.eq sR sL ->
      SubNatRel (@prosa.behavior.schedule.service_on Job PR j sR c)
        (svc_target_service_on Job rsc_ps_to_target j sL (rsc_sigma c)).
    Proof.
      intro Hs. destruct Hs. unfold svc_target_service_on. cbn.
      rewrite rsc_sigma_inv_sigma. exact (sub_nat_rel_canonical _).
    Qed.

    Definition rsc_rel_to_target : SvcProcessorStateRel Job PR rsc_ps_to_target :=
      @Build_SvcProcessorStateRel Job PR rsc_ps_to_target
        (fun sR sL => Lean.eq sR sL) (fun s => s) (fun s => s)
        rsc_sigma rsc_sigma_inv
        (fun s => Logic.eq_refl s) (fun s => @Lean.eq_refl _ s)
        rsc_sigma_inv_sigma (fun c => coq_eq_to_imported_eq _ _ (rsc_sigma_sigma_inv c))
        (fun s => @Lean.eq_refl _ s) (fun s => @Lean.eq_refl _ s)
        rsc_enumeration_rel rsc_tgt_scheduled_rel rsc_tgt_service_rel.

    Lemma rsc_sup_to_target : RsSupplyOnRel PR rsc_ps_to_target rsc_rel_to_target.
    Proof.
      intros sR sL c Hs. cbn in Hs. destruct Hs.
      unfold SUP.supply_target_supply_on. cbn.
      rewrite rsc_sigma_inv_sigma. exact (sub_nat_rel_canonical _).
    Qed.

    Definition rsc_pair_to_target : RsPSPair PR rsc_ps_to_target :=
      {| rs_rel := rsc_rel_to_target; rs_sup := rsc_sup_to_target |}.
  End ToTarget.

  (** *** The cover *)

  Lemma rs_forall_pstate (P : prosa.behavior.schedule.ProcessorState Job -> Prop) (Q : PSL -> SProp) :
    (forall PR PL, RsPSPair PR PL -> PropSPropRel (P PR) (Q PL)) ->
    PropSPropRel (forall PR, P PR) (forall PL, Q PL).
  Proof.
    exact (rsc_forall_cover_type _ _ RsPSPair rsc_ps_to_target rsc_ps_to_source
      rsc_pair_to_target rsc_pair_to_source P Q).
  Qed.
End RsCover.
