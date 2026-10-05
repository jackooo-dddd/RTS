From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSpinFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local proof adapter for the actual imported Spin module. *)
Inductive SpinFalse : SProp := .
Inductive SpinTrue : SProp := spin_true_intro.

Definition spin_false_elim (Q : SProp) (H : SpinFalse) : Q :=
  match H return Q with end.

Definition spin_false_to_strict (H : SpinFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition spin_coq_false_to_target (H : Logic.False) :
    ImportedSpinFull.False :=
  match H return ImportedSpinFull.False with end.

Definition spin_bool_to_imported (b : bool) : ImportedSpinFull.Bool :=
  match b with
  | true => ImportedSpinFull.Bool_true
  | false => ImportedSpinFull.Bool_false
  end.

Definition spin_bool_to_rocq (b : ImportedSpinFull.Bool) : bool :=
  match b with
  | ImportedSpinFull.Bool_true => true
  | ImportedSpinFull.Bool_false => false
  end.

Definition SpinBoolRel (bR : bool) (bL : ImportedSpinFull.Bool) : SProp :=
  Lean.eq (spin_bool_to_imported bR) bL.

Lemma spin_bool_source_roundtrip (b : bool) :
  Logic.eq (spin_bool_to_rocq (spin_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma spin_bool_target_roundtrip (b : ImportedSpinFull.Bool) :
  Lean.eq (spin_bool_to_imported (spin_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition spin_false_ne_true
    (H : Lean.eq ImportedSpinFull.Bool_false ImportedSpinFull.Bool_true) :
    SpinFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedSpinFull.Bool_false => SpinTrue
    | ImportedSpinFull.Bool_true => SpinFalse
    end
  with
  | Lean.eq_refl => spin_true_intro
  end.

Lemma spin_bool_truth_correspondence bR bL :
  SpinBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedSpinFull.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (spin_false_to_strict (spin_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition spin_decidable_eq (T : eqType) : ImportedSpinFull.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedSpinFull.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedSpinFull.Decidable_isFalse (Lean.eq x y)
        (fun HL => spin_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.
