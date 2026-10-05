From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTactics.
From FoundationCertificates Require Import PropSPropFoundation.
From prosa Require Import util.tactics.

Definition RocqModusPonensStatement (P Q : Prop) : Prop :=
  P -> (P -> Q) -> Q.

Definition ImportedModusPonensStatement (P Q : SProp) : SProp :=
  P -> (P -> Q) -> Q.

(** Structural logical-relation proof for the exact polymorphic logical shell
    of the official and imported [modusponens] theorem types.  It does not use
    either theorem proof constant. *)
Lemma modusponens_statement_certificate :
  forall (PR QR : Prop) (PL QL : SProp),
    PropSPropRel PR PL ->
    PropSPropRel QR QL ->
    PropSPropRel
      (RocqModusPonensStatement PR QR)
      (ImportedModusPonensStatement PL QL).
Proof.
  intros PR QR PL QL HP HQ.
  constructor.
  - intros hR pL hPLQL.
    apply (prop_to_sprop _ _ HQ).
    apply hR.
    + exact (sprop_to_prop _ _ HP pL).
    + intro pR.
      apply (sprop_to_prop _ _ HQ).
      apply hPLQL.
      exact (prop_to_sprop _ _ HP pR).
  - intros hL pR hPRQR.
    apply (sprop_to_prop _ _ HQ).
    apply hL.
    + exact (prop_to_sprop _ _ HP pR).
    + intro pL.
      apply (prop_to_sprop _ _ HQ).
      apply hPRQR.
      exact (sprop_to_prop _ _ HP pL).
Qed.

