From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import TransformPrefixSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTransformPrefix ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedTransformPrefix.
Module S := TransformPrefixSemanticSource.TransformPrefixSemanticSource.

(** Certificates for [analysis/transform/prefix.v].

    Source side: the extracted byte-identical [prefix_map] block and the two
    extracted lemma statements specialised at their leading inputs (job
    type, processor state, the schedule predicates [P]/[Q] and the
    transformation [f]); target side: the compiled Lean declarations.
    Processor states are related by the accepted two-sided
    [SvcProcessorStateRel]; schedules functionally through its state
    conversion ([PfxScheduleFunRel]), covered in both directions with the
    conversion roundtrips; [f] preserves [PfxScheduleFunRel] on related
    instants; [P]/[Q] are related on related schedules (and instants).  The
    structural recursion of [prefix_map] is related through kernel-checked
    Lean case equations exported with the artifact.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma pfx_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma pfx_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma pfx_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Section Prefix.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.

  Definition PfxScheduleFunRel (schedR : SchedR) (schedL : SchedL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      Lean.eq (svc_ps_state_to_target Job PStateR PStateL R (schedR tR)) (schedL tL).

  Definition pfx_schedule_to_target (schedR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition pfx_schedule_to_source (schedL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma pfx_schedule_to_target_rel schedR : PfxScheduleFunRel schedR (pfx_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold pfx_schedule_to_target.
    rewrite (pfx_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pfx_schedule_to_source_rel schedL : PfxScheduleFunRel (pfx_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold pfx_schedule_to_source.
    exact (sub_imported_eq_trans _ _ _
      (svc_ps_state_target_roundtrip Job PStateR PStateL R _)
      (sub_imported_eq_congr schedL _ _ Ht)).
  Qed.

  Let cover_schedule :=
    pfx_forall_cover_sprop _ _ PfxScheduleFunRel pfx_schedule_to_target pfx_schedule_to_source
      pfx_schedule_to_target_rel pfx_schedule_to_source_rel.

  Variable fR : SchedR -> nat -> SchedR.
  Variable fL : SchedL -> Lean.Nat -> SchedL.
  Hypothesis Hf : forall sR sL, PfxScheduleFunRel sR sL ->
    forall tR tL, SubNatRel tR tL -> PfxScheduleFunRel (fR sR tR) (fL sL tL).

  Lemma pfx_prefix_map_canonical (sR : SchedR) (sL : SchedL) (Hs : PfxScheduleFunRel sR sL) (h : nat) :
    PfxScheduleFunRel (@S.prefix_map Job PStateR sR fR h)
      (I.Prosa_Analysis_Transform_Prefix_prefix_map Job dJ PStateL sL fL (sub_nat_to_imported h)).
  Proof.
    induction h as [|h IH].
    - cbn [S.prefix_map sub_nat_to_imported].
      exact (pfx_lean_transport (fun s => PfxScheduleFunRel sR s) _ _
        (sub_imported_eq_sym _ _
          (I.Prosa_Validation_TransformPrefixInterface_production_prefix_map_zero Job dJ PStateL sL fL)) Hs).
    - cbn [S.prefix_map sub_nat_to_imported].
      exact (pfx_lean_transport (fun s => PfxScheduleFunRel _ s) _ _
        (sub_imported_eq_sym _ _
          (I.Prosa_Validation_TransformPrefixInterface_production_prefix_map_succ Job dJ PStateL sL fL
            (sub_nat_to_imported h)))
        (Hf _ _ IH h _ (sub_nat_rel_canonical h))).
  Qed.

  Theorem prefix_map_correspondence (sR : SchedR) (sL : SchedL) (Hs : PfxScheduleFunRel sR sL)
      (hR : nat) (hL : Lean.Nat) (Hh : SubNatRel hR hL) :
    PfxScheduleFunRel (@S.prefix_map Job PStateR sR fR hR)
      (I.Prosa_Analysis_Transform_Prefix_prefix_map Job dJ PStateL sL fL hL).
  Proof.
    exact (pfx_lean_transport
      (fun h => PfxScheduleFunRel (@S.prefix_map Job PStateR sR fR hR)
        (I.Prosa_Analysis_Transform_Prefix_prefix_map Job dJ PStateL sL fL h)) _ _ Hh
      (pfx_prefix_map_canonical sR sL Hs hR)).
  Qed.

  Variable PR : SchedR -> Prop.
  Variable PL : SchedL -> SProp.
  Hypothesis HP : forall sR sL, PfxScheduleFunRel sR sL -> PropSPropRel (PR sR) (PL sL).

  Definition src_prefix_map_property_invariance : Prop :=
    ltac:(body_of (fun s : S.statement_prefix_map_property_invariance => s Job PStateR PR fR)).
  Definition tgt_prefix_map_property_invariance : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Transform_Prefix_prefix_map_property_invariance
      Job dJ PStateL PL fL)).
  Theorem prefix_map_property_invariance_correspondence :
    PropSPropRel src_prefix_map_property_invariance tgt_prefix_map_property_invariance.
  Proof.
    apply ar_imp_correspondence.
    - apply cover_schedule. intros sR sL Hs.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (HP _ _ Hs)|].
      exact (HP _ _ (Hf _ _ Hs _ _ Ht)).
    - apply cover_schedule. intros sR sL Hs.
      apply ar_forall_nat_correspondence. intros hR hL Hh.
      apply ar_imp_correspondence; [exact (HP _ _ Hs)|].
      exact (HP _ _ (prefix_map_correspondence sR sL Hs hR hL Hh)).
  Qed.

  Variable QR : SchedR -> nat -> Prop.
  Variable QL : SchedL -> Lean.Nat -> SProp.
  Hypothesis HQ : forall sR sL, PfxScheduleFunRel sR sL ->
    forall tR tL, SubNatRel tR tL -> PropSPropRel (QR sR tR) (QL sL tL).

  Definition src_prefix_map_pointwise_property : Prop :=
    ltac:(body_of (fun s : S.statement_prefix_map_pointwise_property => s Job PStateR PR QR fR)).
  Definition tgt_prefix_map_pointwise_property : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Transform_Prefix_prefix_map_pointwise_property
      Job dJ PStateL PL QL fL)).
  Theorem prefix_map_pointwise_property_correspondence :
    PropSPropRel src_prefix_map_pointwise_property tgt_prefix_map_pointwise_property.
  Proof.
    apply ar_imp_correspondence.
    { apply cover_schedule. intros sR sL Hs.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (HP _ _ Hs)|].
      exact (HP _ _ (Hf _ _ Hs _ _ Ht)). }
    apply ar_imp_correspondence.
    { apply cover_schedule. intros sR sL Hs.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (HP _ _ Hs)|].
      apply ar_imp_correspondence.
      - apply ar_forall_nat_correspondence. intros uR uL Hu.
        apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hu Ht)|].
        exact (HQ _ _ Hs _ _ Hu).
      - apply ar_forall_nat_correspondence. intros uR uL Hu.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hu Ht)|].
        exact (HQ _ _ (Hf _ _ Hs _ _ Ht) _ _ Hu). }
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence; [exact (HP _ _ Hs)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh)|].
    exact (HQ _ _ (prefix_map_correspondence sR sL Hs hR hL Hh) _ _ Ht).
  Qed.
End Prefix.
