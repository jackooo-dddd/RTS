(* Copy of the accepted certificates/implementation/ArrivalBoundCorrespondence.v, re-bound to this export: the
   source side is the pinned arrival_bound.v (compiled under its Rocq 9.3 import-compatibility patch) instead of
   the accepted definition-extracted OfficialArrivalBound signature; the adapter between the two earlier separate
   exports is replaced by the prefix maps of EacFullCorrespondence (one export here); the Lean-eqdef Boolean
   correspondence and the eqn_task_arrivals_bound statement correspondence (not part of this file) are dropped,
   as are the Print Assumptions commands. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedImplTask.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
From FoundationCertificates Require Import EacFullCorrespondence.
From prosa Require Import implementation.definitions.arrival_bound.

(** The prefix type is the extrapolated-curve prefix of this same export, so the accepted adapter between the
    two separate earlier exports is replaced by the EAC prefix maps and roundtrips. *)
Definition ab_prefix_from_source pR := eac_imported_prefix pR.
Definition ab_prefix_to_source pL := eac_rocq_prefix pL.
Lemma ab_prefix_source_roundtrip pR :
  Logic.eq (ab_prefix_to_source (ab_prefix_from_source pR)) pR.
Proof. exact (eac_prefix_rocq_roundtrip pR). Qed.
Lemma ab_prefix_target_roundtrip pL :
  Lean.eq (ab_prefix_from_source (ab_prefix_to_source pL)) pL.
Proof. exact (eac_prefix_imported_roundtrip pL). Qed.

Definition AbSource := prosa.implementation.definitions.arrival_bound.task_arrivals_bound.
Definition AbTarget :=
  ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound.

Definition ab_export_bound (xR : AbSource) : AbTarget :=
  match xR with
  | prosa.implementation.definitions.arrival_bound.Periodic n =>
      ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
        (sub_nat_to_imported n)
  | prosa.implementation.definitions.arrival_bound.Sporadic n =>
      ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
        (sub_nat_to_imported n)
  | prosa.implementation.definitions.arrival_bound.ArrivalPrefix p =>
      ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
        (ab_prefix_from_source p)
  end.

Definition ab_import_bound (xL : AbTarget) : AbSource :=
  match xL with
  | ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic n =>
      prosa.implementation.definitions.arrival_bound.Periodic (sub_nat_to_rocq n)
  | ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic n =>
      prosa.implementation.definitions.arrival_bound.Sporadic (sub_nat_to_rocq n)
  | ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix p =>
      prosa.implementation.definitions.arrival_bound.ArrivalPrefix
        (ab_prefix_to_source p)
  end.

Definition AbRel (xR : AbSource) (xL : AbTarget) : SProp :=
  Lean.eq (ab_export_bound xR) xL.

Lemma ab_source_roundtrip xR :
  Logic.eq (ab_import_bound (ab_export_bound xR)) xR.
Proof.
  destruct xR as [n|n|p]; simpl.
  - rewrite (sub_nat_rocq_roundtrip n). reflexivity.
  - rewrite (sub_nat_rocq_roundtrip n). reflexivity.
  - rewrite (ab_prefix_source_roundtrip p). reflexivity.
Qed.

Lemma ab_target_roundtrip xL :
  AbRel (ab_import_bound xL) xL.
Proof.
  destruct xL as [n|n|p]; simpl.
  - exact (sub_imported_eq_congr
      ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
      _ _ (sub_nat_imported_roundtrip n)).
  - exact (sub_imported_eq_congr
      ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
      _ _ (sub_nat_imported_roundtrip n)).
  - exact (sub_imported_eq_congr
      ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
      _ _ (ab_prefix_target_roundtrip p)).
Qed.

Lemma ab_source_constructor_periodic nR nL :
  SubNatRel nR nL ->
  AbRel (prosa.implementation.definitions.arrival_bound.Periodic nR)
    (ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic nL).
Proof.
  intro Hn. exact (sub_imported_eq_congr
    ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
    _ _ Hn).
Qed.

Lemma ab_source_constructor_sporadic nR nL :
  SubNatRel nR nL ->
  AbRel (prosa.implementation.definitions.arrival_bound.Sporadic nR)
    (ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic nL).
Proof.
  intro Hn. exact (sub_imported_eq_congr
    ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
    _ _ Hn).
Qed.

Lemma ab_source_constructor_prefix pR pL :
  Lean.eq (ab_prefix_from_source pR) pL ->
  AbRel (prosa.implementation.definitions.arrival_bound.ArrivalPrefix pR)
    (ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix pL).
Proof.
  intro Hp. exact (sub_imported_eq_congr
    ImportedImplTask.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
    _ _ Hp).
Qed.

(** Proved from the byte-identical source definition, not from the source
    [eqn_task_arrivals_bound] theorem proof. *)
Lemma ab_source_eqdef_iff (x y : AbSource) :
  is_true (prosa.implementation.definitions.arrival_bound.task_arrivals_bound_eqdef x y)
    <-> Logic.eq x y.
Proof.
  destruct x as [a|a|a]; destruct y as [b|b|b]; simpl;
    try (split; [intro H; discriminate H | intro H; discriminate H]);
    split.
  - move/eqP=>H. subst. reflexivity.
  - intro H. inversion H; subst. apply/eqP. reflexivity.
  - move/eqP=>H. subst. reflexivity.
  - intro H. inversion H; subst. apply/eqP. reflexivity.
  - move/eqP=>H. subst. reflexivity.
  - intro H. inversion H; subst. apply/eqP. reflexivity.
Qed.

Lemma ab_equality_correspondence xR xL yR yL :
  AbRel xR xL -> AbRel yR yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy.
    exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits.
    destruct Hx. destruct Hy.
    have Hdecoded := f_equal ab_import_bound
      (imported_eq_to_coq_eq _ _ Hxy).
    rewrite (ab_source_roundtrip xR) (ab_source_roundtrip yR)
      in Hdecoded.
    exact Hdecoded.
Qed.

Definition ab_bool_to_imported (b : bool) : ImportedImplTask.Bool :=
  match b with
  | true => ImportedImplTask.Bool_true
  | false => ImportedImplTask.Bool_false
  end.

Definition AbBoolRel (bR : bool) (bL : ImportedImplTask.Bool) : SProp :=
  Lean.eq (ab_bool_to_imported bR) bL.

Definition ab_target_false_elim (Q : SProp)
    (H : ImportedImplTask.False) : Q :=
  match H return Q with end.

Definition ab_rocq_false_to_target (H : Logic.False) :
    ImportedImplTask.False :=
  match H return ImportedImplTask.False with end.

Lemma ab_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedImplTask.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  AbBoolRel bR (ImportedImplTask.Decidable_decide Q d).
Proof.
  intro Hrel. unfold AbBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (ab_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ab_target_false_elim _ (ab_rocq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

(** The source [Equality.axiom] is an informative [reflect] view in [Type].
    The target has a separately imported [BoolReflect] family.  Both maps
    preserve the constructors and do not invoke either public theorem proof. *)
Definition ab_reflect_forward (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedImplTask.Bool)
    (HP : PropSPropRel PR PL) (Hb : AbBoolRel bR bL) :
    reflect PR bR ->
    ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isTrue
      PL (prop_to_sprop _ _ HP Htrue)).
  - exact (ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isFalse
      PL (fun HL => ab_rocq_false_to_target
        (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition ab_bool_from_imported (b : ImportedImplTask.Bool) : bool :=
  match b with
  | ImportedImplTask.Bool_true => true
  | ImportedImplTask.Bool_false => false
  end.

Definition ab_reflect_backward_at_bool (PR : Prop) (PL : SProp)
    (HP : PropSPropRel PR PL) (bL : ImportedImplTask.Bool) :
    ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
    reflect PR (ab_bool_from_imported bL) :=
  fun HL =>
    match HL in
      ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect _ b
      return reflect PR (ab_bool_from_imported b) with
    | ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isTrue Htrue =>
        ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR =>
          interpret_strict Logic.False
            (ab_target_false_elim _
              (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition ab_reflect_backward (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedImplTask.Bool)
    (HP : PropSPropRel PR PL) (Hb : AbBoolRel bR bL) :
    ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
    reflect PR bR.
Proof.
  destruct Hb. destruct bR; cbn;
    exact (ab_reflect_backward_at_bool PR PL HP _).
Defined.

Definition AbReflectTypeRel (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedImplTask.Bool) : Type :=
  Datatypes.prod
    (reflect PR bR ->
      ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL)
    (ImportedImplTask.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
      reflect PR bR).
