From mathcomp Require Import ssreflect ssrbool.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJitterPublic.
From FoundationCertificates Require Import PropSPropFoundation
  SubadditivityNatCorrespondence.

(** This adapter uses the imported Bool and Decidable constructors from the
    actual, two-public-root Jitter artifact. *)
Inductive JiFalse : SProp := .

Definition ji_false_elim (Q : SProp) (H : JiFalse) : Q :=
  match H return Q with end.

Definition ji_coq_false_to_target (H : Logic.False) :
    ImportedJitterPublic.False :=
  match H return ImportedJitterPublic.False with end.

Definition ji_bool_to_imported (b : bool) : ImportedJitterPublic.Bool :=
  match b with
  | true => ImportedJitterPublic.Bool_true
  | false => ImportedJitterPublic.Bool_false
  end.

Definition ji_bool_to_rocq (b : ImportedJitterPublic.Bool) : bool :=
  match b with
  | ImportedJitterPublic.Bool_true => true
  | ImportedJitterPublic.Bool_false => false
  end.

Definition JiBoolRel (bR : bool) (bL : ImportedJitterPublic.Bool) : SProp :=
  Lean.eq (ji_bool_to_imported bR) bL.

Lemma ji_bool_source_roundtrip b :
  Logic.eq (ji_bool_to_rocq (ji_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ji_bool_target_roundtrip b :
  Lean.eq (ji_bool_to_imported (ji_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition ji_target_false_elim (Q : SProp)
    (H : ImportedJitterPublic.False) : Q :=
  match H return Q with end.

Lemma ji_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedJitterPublic.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  JiBoolRel bR (ImportedJitterPublic.Decidable_decide Q d).
Proof.
  intro Hrel. unfold JiBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (ji_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ji_target_false_elim _ (ji_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Print Assumptions ji_bool_source_roundtrip.
Print Assumptions ji_bool_target_roundtrip.
Print Assumptions ji_decide_bool_correspondence.
