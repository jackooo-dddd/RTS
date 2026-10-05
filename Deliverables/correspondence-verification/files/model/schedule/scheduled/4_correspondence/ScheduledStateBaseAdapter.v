(** Adapted from accepted EdfBaseAdapter.v (SHA-256
    4916a4a40d389d79b806d3b71986b8c5c5d413c239b655fb6202f8e1c24122ef).
    The imported identity changes, and the selected DecidableEq is shared
    definitionally with ReadyArrivalBaseAdapter in this artifact. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduledFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ReadyArrivalBaseAdapter.

(** Artifact-local Bool/equality adapter for the actual imported Scheduled
    module. This replays the accepted EDF operation pattern with one selected
    equality instance shared with the ArrivalSequence adapter. *)

Inductive EdfFalse : SProp := .
Inductive EdfTrue : SProp := edf_true_intro.

Definition edf_false_elim (Q : SProp) (H : EdfFalse) : Q :=
  match H return Q with end.

Definition edf_false_to_strict (H : EdfFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition edf_coq_false_to_target (H : Logic.False) :
    ImportedScheduledFull.False :=
  match H return ImportedScheduledFull.False with end.

Definition edf_bool_to_imported (b : bool) : ImportedScheduledFull.Bool :=
  match b with
  | true => ImportedScheduledFull.Bool_true
  | false => ImportedScheduledFull.Bool_false
  end.

Definition edf_bool_to_rocq (b : ImportedScheduledFull.Bool) : bool :=
  match b with
  | ImportedScheduledFull.Bool_true => true
  | ImportedScheduledFull.Bool_false => false
  end.

Definition EdfBoolRel (bR : bool) (bL : ImportedScheduledFull.Bool) : SProp :=
  Lean.eq (edf_bool_to_imported bR) bL.

Lemma edf_bool_source_roundtrip (b : bool) :
  Logic.eq (edf_bool_to_rocq (edf_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma edf_bool_target_roundtrip (b : ImportedScheduledFull.Bool) :
  Lean.eq (edf_bool_to_imported (edf_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition edf_false_ne_true
    (H : Lean.eq ImportedScheduledFull.Bool_false ImportedScheduledFull.Bool_true) :
    EdfFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedScheduledFull.Bool_false => EdfTrue
    | ImportedScheduledFull.Bool_true => EdfFalse
    end
  with
  | Lean.eq_refl => edf_true_intro
  end.

Lemma edf_bool_truth_correspondence bR bL :
  EdfBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedScheduledFull.Bool_true).
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

(** The same selected equality instance is used in the arrival-sequence and
    processor-state observations of this one imported artifact. *)
Definition edf_decidable_eq (T : eqType) : ImportedScheduledFull.DecidableEq T :=
  ar_decidable_eq T.
