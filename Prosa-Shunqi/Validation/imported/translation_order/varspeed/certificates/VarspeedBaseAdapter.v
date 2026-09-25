From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedVarspeedFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local adapters for the actual ImportedVarspeedFull datatype
    identities. No source or target business theorem is assumed. *)
Inductive VsFalse : SProp := .
Inductive VsTrue : SProp := vs_true_intro.

Definition vs_false_elim (Q : SProp) (H : VsFalse) : Q :=
  match H return Q with end.

Definition vs_false_to_strict (H : VsFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition vs_coq_false_to_target (H : Logic.False) :
    ImportedVarspeedFull.False := match H return ImportedVarspeedFull.False with end.

Definition vs_bool_to_imported (b : bool) : ImportedVarspeedFull.Bool :=
  match b with
  | true => ImportedVarspeedFull.Bool_true
  | false => ImportedVarspeedFull.Bool_false
  end.

Definition vs_bool_to_rocq (b : ImportedVarspeedFull.Bool) : bool :=
  match b with
  | ImportedVarspeedFull.Bool_true => true
  | ImportedVarspeedFull.Bool_false => false
  end.

Definition VsBoolRel (bR : bool) (bL : ImportedVarspeedFull.Bool) : SProp :=
  Lean.eq (vs_bool_to_imported bR) bL.

Lemma vs_bool_source_roundtrip (b : bool) :
  Logic.eq (vs_bool_to_rocq (vs_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma vs_bool_target_roundtrip (b : ImportedVarspeedFull.Bool) :
  Lean.eq (vs_bool_to_imported (vs_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition vs_false_ne_true
    (H : Lean.eq ImportedVarspeedFull.Bool_false ImportedVarspeedFull.Bool_true) :
    VsFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedVarspeedFull.Bool_false => VsTrue
    | ImportedVarspeedFull.Bool_true => VsFalse
    end
  with
  | Lean.eq_refl => vs_true_intro
  end.

Lemma vs_bool_truth_correspondence bR bL :
  VsBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedVarspeedFull.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (vs_false_to_strict (vs_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition vs_decidable_eq (T : eqType) : ImportedVarspeedFull.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedVarspeedFull.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedVarspeedFull.Decidable_isFalse (Lean.eq x y)
        (fun HL => vs_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Lemma vs_job_equality_truth (Job : eqType) (x y : Job) :
  PropSPropRel (is_true (x == y)) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - move/eqP=> H. exact (coq_eq_to_imported_eq x y H).
  - intro H. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y H).
Qed.

Definition vs_target_false_elim (Q : SProp)
    (H : ImportedVarspeedFull.False) : Q :=
  match H return Q with end.

Lemma vs_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedVarspeedFull.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  VsBoolRel bR (ImportedVarspeedFull.Decidable_decide Q d).
Proof.
  intro Hrel. unfold VsBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (vs_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (vs_target_false_elim _ (vs_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma vs_bool_false_correspondence (bR : bool)
    (bL : ImportedVarspeedFull.Bool) :
  VsBoolRel bR bL ->
  PropSPropRel (is_true (~~ bR))
    (Lean.eq bL ImportedVarspeedFull.Bool_false).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Hfalse. destruct bR, bL; cbn in *.
    + discriminate Hfalse.
    + discriminate Hfalse.
    + exact (@Lean.eq_refl _ _).
    + exact (vs_false_elim _ (vs_false_ne_true Hb)).
  - intro Hfalse. destruct bR, bL; cbn in *.
    + exact (vs_false_elim _ (vs_false_ne_true
        (sub_imported_eq_sym _ _ Hb))).
    + exact (vs_false_elim _ (vs_false_ne_true
        (sub_imported_eq_sym _ _ Hfalse))).
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + exact (vs_false_elim _ (vs_false_ne_true Hb)).
Qed.
