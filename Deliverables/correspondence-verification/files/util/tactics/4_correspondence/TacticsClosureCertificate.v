From mathcomp Require Import ssreflect ssrbool eqtype.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTactics.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation EqTypeCorrespondence.
From prosa Require Import util.tactics.

Definition RocqNeqPStatement (T : eqType) (x y : T) : Set :=
  reflect (x <> y) (x != y).

Definition ImportedNeqPStatement (T : eqType) (x y : T) : SProp :=
  ImportedTactics.Iff
    (Lean.eq
      (ImportedTactics.Decidable_decide (ImportedTactics.Ne T x y)
        (ImportedTactics.instDecidableNot (Lean.eq x y)
          (eqtype_to_tactics_decidable_eq T x y)))
      ImportedTactics.Bool_true)
    (ImportedTactics.Ne T x y).

(** Exact-type guards are separate from the correspondence certificate, so
    the latter has no source- or target-theorem self dependency. *)
Definition rocq_neqP_type_guard (T : eqType) (x y : T) :
    RocqNeqPStatement T x y := @prosa.util.tactics.neqP T x y.

Definition imported_neqP_type_guard (T : eqType) (x y : T) :
    ImportedNeqPStatement T x y :=
  Prosa_Util_Tactics_neqP T (eqtype_to_tactics_decidable_eq T) x y.

Definition tactics_false_ne_true
    (H : Lean.eq ImportedTactics.Bool_false ImportedTactics.Bool_true) :
    EqValidationFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedTactics.Bool_false => EqValidationTrue
    | ImportedTactics.Bool_true => EqValidationFalse
    end
  with
  | Lean.eq_refl => eq_validation_I
  end.

Lemma neqP_statement_correspondence_certificate :
  forall (T : eqType) (x y : T),
    SetSPropRel (RocqNeqPStatement T x y)
      (ImportedNeqPStatement T x y).
Proof.
  intros T x y. constructor.
  - intro Hsource.
    unfold ImportedNeqPStatement, eqtype_to_tactics_decidable_eq.
    destruct (@eqP T x y) as [Heq | Hneq]; cbn.
    + apply ImportedTactics.Iff_intro.
      * intro Hfalse. exact (eq_false_elim _ (tactics_false_ne_true Hfalse)).
      * intro Hne. exact (tactics_false_elim _
          (Hne (coq_eq_to_imported_eq x y Heq))).
    + apply ImportedTactics.Iff_intro.
      * intro Hdecide. intro HeqL.
        exact (coq_false_to_tactics_false
          (Hneq (imported_eq_to_coq_eq x y HeqL))).
      * intro Hne. exact (@Lean.eq_refl ImportedTactics.Bool ImportedTactics.Bool_true).
  - intro Htarget.
    unfold RocqNeqPStatement.
    destruct (@eqP T x y) as [Heq | Hneq].
    + apply ReflectF. intro H. exact (H Heq).
    + apply ReflectT. exact Hneq.
Qed.

Print Assumptions neqP_statement_correspondence_certificate.
