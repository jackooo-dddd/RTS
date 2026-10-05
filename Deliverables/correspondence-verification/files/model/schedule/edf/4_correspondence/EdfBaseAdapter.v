From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedEdfFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local Bool/equality adapter for the actual imported EDF module.
    This specializes the already accepted ServiceBaseAdapter pattern. *)

Inductive EdfFalse : SProp := .
Inductive EdfTrue : SProp := edf_true_intro.

Definition edf_false_elim (Q : SProp) (H : EdfFalse) : Q :=
  match H return Q with end.

Definition edf_false_to_strict (H : EdfFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition edf_coq_false_to_target (H : Logic.False) :
    ImportedEdfFull.False :=
  match H return ImportedEdfFull.False with end.

Definition edf_bool_to_imported (b : bool) : ImportedEdfFull.Bool :=
  match b with
  | true => ImportedEdfFull.Bool_true
  | false => ImportedEdfFull.Bool_false
  end.

Definition edf_bool_to_rocq (b : ImportedEdfFull.Bool) : bool :=
  match b with
  | ImportedEdfFull.Bool_true => true
  | ImportedEdfFull.Bool_false => false
  end.

Definition EdfBoolRel (bR : bool) (bL : ImportedEdfFull.Bool) : SProp :=
  Lean.eq (edf_bool_to_imported bR) bL.

Lemma edf_bool_source_roundtrip (b : bool) :
  Logic.eq (edf_bool_to_rocq (edf_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma edf_bool_target_roundtrip (b : ImportedEdfFull.Bool) :
  Lean.eq (edf_bool_to_imported (edf_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition edf_false_ne_true
    (H : Lean.eq ImportedEdfFull.Bool_false ImportedEdfFull.Bool_true) :
    EdfFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedEdfFull.Bool_false => EdfTrue
    | ImportedEdfFull.Bool_true => EdfFalse
    end
  with
  | Lean.eq_refl => edf_true_intro
  end.

Lemma edf_bool_truth_correspondence bR bL :
  EdfBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedEdfFull.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (edf_false_to_strict (edf_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition edf_decidable_eq (T : eqType) : ImportedEdfFull.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedEdfFull.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedEdfFull.Decidable_isFalse (Lean.eq x y)
        (fun HL => edf_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.
