From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedArrivalBound.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
From ImplementationCertificates Require Import ArrivalBoundArtifactAdapter.
Require Import OfficialArrivalBound.

Definition AbSource := OfficialArrivalBound.OfficialArrivalBound.task_arrivals_bound.
Definition AbTarget :=
  ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound.

Definition ab_export_bound (xR : AbSource) : AbTarget :=
  match xR with
  | OfficialArrivalBound.OfficialArrivalBound.Periodic n =>
      ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
        (sub_nat_to_imported n)
  | OfficialArrivalBound.OfficialArrivalBound.Sporadic n =>
      ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
        (sub_nat_to_imported n)
  | OfficialArrivalBound.OfficialArrivalBound.ArrivalPrefix p =>
      ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
        (ab_prefix_from_source p)
  end.

Definition ab_import_bound (xL : AbTarget) : AbSource :=
  match xL with
  | ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic n =>
      OfficialArrivalBound.OfficialArrivalBound.Periodic (sub_nat_to_rocq n)
  | ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic n =>
      OfficialArrivalBound.OfficialArrivalBound.Sporadic (sub_nat_to_rocq n)
  | ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix p =>
      OfficialArrivalBound.OfficialArrivalBound.ArrivalPrefix
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
      ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
      _ _ (sub_nat_imported_roundtrip n)).
  - exact (sub_imported_eq_congr
      ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
      _ _ (sub_nat_imported_roundtrip n)).
  - exact (sub_imported_eq_congr
      ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
      _ _ (ab_prefix_target_roundtrip p)).
Qed.

Lemma ab_source_constructor_periodic nR nL :
  SubNatRel nR nL ->
  AbRel (OfficialArrivalBound.OfficialArrivalBound.Periodic nR)
    (ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic nL).
Proof.
  intro Hn. exact (sub_imported_eq_congr
    ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
    _ _ Hn).
Qed.

Lemma ab_source_constructor_sporadic nR nL :
  SubNatRel nR nL ->
  AbRel (OfficialArrivalBound.OfficialArrivalBound.Sporadic nR)
    (ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic nL).
Proof.
  intro Hn. exact (sub_imported_eq_congr
    ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
    _ _ Hn).
Qed.

Lemma ab_source_constructor_prefix pR pL :
  Lean.eq (ab_prefix_from_source pR) pL ->
  AbRel (OfficialArrivalBound.OfficialArrivalBound.ArrivalPrefix pR)
    (ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix pL).
Proof.
  intro Hp. exact (sub_imported_eq_congr
    ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
    _ _ Hp).
Qed.

(** Proved from the byte-identical source definition, not from the source
    [eqn_task_arrivals_bound] theorem proof. *)
Lemma ab_source_eqdef_iff (x y : AbSource) :
  is_true (OfficialArrivalBound.OfficialArrivalBound.task_arrivals_bound_eqdef x y)
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

Definition ab_bool_to_imported (b : bool) : ImportedArrivalBound.Bool :=
  match b with
  | true => ImportedArrivalBound.Bool_true
  | false => ImportedArrivalBound.Bool_false
  end.

Definition AbBoolRel (bR : bool) (bL : ImportedArrivalBound.Bool) : SProp :=
  Lean.eq (ab_bool_to_imported bR) bL.

Definition ab_target_false_elim (Q : SProp)
    (H : ImportedArrivalBound.False) : Q :=
  match H return Q with end.

Definition ab_rocq_false_to_target (H : Logic.False) :
    ImportedArrivalBound.False :=
  match H return ImportedArrivalBound.False with end.

Lemma ab_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedArrivalBound.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  AbBoolRel bR (ImportedArrivalBound.Decidable_decide Q d).
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

Lemma ab_eqdef_bool_correspondence xR xL yR yL :
  AbRel xR xL -> AbRel yR yL ->
  AbBoolRel
    (OfficialArrivalBound.OfficialArrivalBound.task_arrivals_bound_eqdef xR yR)
    (ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_eqdef xL yL).
Proof.
  intros Hx Hy.
  have Heq := ab_equality_correspondence xR xL yR yL Hx Hy.
  have Hsource := ab_source_eqdef_iff xR yR.
  have Hlogic : PropSPropRel
      (is_true (OfficialArrivalBound.OfficialArrivalBound.task_arrivals_bound_eqdef xR yR))
      (Lean.eq xL yL).
  { apply prop_sprop_rel_intro.
    - intro H. apply (prop_to_sprop _ _ Heq).
      exact (proj1 Hsource H).
    - intro H. apply strictly_inhabits. apply (proj2 Hsource).
      exact (sprop_to_prop _ _ Heq H). }
  have Hdecide := ab_decide_bool_correspondence
    (OfficialArrivalBound.OfficialArrivalBound.task_arrivals_bound_eqdef xR yR)
    (Lean.eq xL yL)
    (ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_instDecidableEqTask_arrivals_bound xL yL)
    Hlogic.
  exact (sub_imported_eq_trans _ _ _ Hdecide
    (sub_imported_eq_sym _ _
      (ImportedArrivalBound._private_Prosa_Implementation_Definitions_ArrivalBound0_Prosa_Implementation_Definitions_ArrivalBound_eqdef_eq_decide
        xL yL))).
Qed.

(** The source [Equality.axiom] is an informative [reflect] view in [Type].
    The target has a separately imported [BoolReflect] family.  Both maps
    preserve the constructors and do not invoke either public theorem proof. *)
Definition ab_reflect_forward (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedArrivalBound.Bool)
    (HP : PropSPropRel PR PL) (Hb : AbBoolRel bR bL) :
    reflect PR bR ->
    ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isTrue
      PL (prop_to_sprop _ _ HP Htrue)).
  - exact (ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isFalse
      PL (fun HL => ab_rocq_false_to_target
        (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition ab_bool_from_imported (b : ImportedArrivalBound.Bool) : bool :=
  match b with
  | ImportedArrivalBound.Bool_true => true
  | ImportedArrivalBound.Bool_false => false
  end.

Definition ab_reflect_backward_at_bool (PR : Prop) (PL : SProp)
    (HP : PropSPropRel PR PL) (bL : ImportedArrivalBound.Bool) :
    ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
    reflect PR (ab_bool_from_imported bL) :=
  fun HL =>
    match HL in
      ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect _ b
      return reflect PR (ab_bool_from_imported b) with
    | ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isTrue Htrue =>
        ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR =>
          interpret_strict Logic.False
            (ab_target_false_elim _
              (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition ab_reflect_backward (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedArrivalBound.Bool)
    (HP : PropSPropRel PR PL) (Hb : AbBoolRel bR bL) :
    ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
    reflect PR bR.
Proof.
  destruct Hb. destruct bR; cbn;
    exact (ab_reflect_backward_at_bool PR PL HP _).
Defined.

Definition AbReflectTypeRel (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedArrivalBound.Bool) : Type :=
  Datatypes.prod
    (reflect PR bR ->
      ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL)
    (ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
      reflect PR bR).

Definition ab_eqn_task_arrivals_bound_statement_correspondence :
  forall xR yR xL yL,
    AbRel xR xL -> AbRel yR yL ->
    AbReflectTypeRel
      (Logic.eq xR yR) (Lean.eq xL yL)
      (OfficialArrivalBound.OfficialArrivalBound.task_arrivals_bound_eqdef xR yR)
      (ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_eqdef xL yL) :=
  fun xR yR xL yL Hx Hy =>
    let Hprop := ab_equality_correspondence xR xL yR yL Hx Hy in
    let Hbool := ab_eqdef_bool_correspondence xR xL yR yL Hx Hy in
    Datatypes.pair
      (ab_reflect_forward _ _ _ _ Hprop Hbool)
      (ab_reflect_backward _ _ _ _ Hprop Hbool).

Print Assumptions ab_source_roundtrip.
Print Assumptions ab_target_roundtrip.
Print Assumptions ab_source_eqdef_iff.
Print Assumptions ab_eqdef_bool_correspondence.
Print Assumptions ab_eqn_task_arrivals_bound_statement_correspondence.
