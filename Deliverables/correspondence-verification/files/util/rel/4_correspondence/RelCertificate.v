From mathcomp Require Import ssreflect ssrbool eqtype seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRel.
From FoundationCertificates Require Import PropSPropFoundation.
From prosa Require Import util.rel.

(** Parametric correspondence for a higher-order Boolean relation.  The
    pointwise truth relation is exactly the semantic relation required for the
    two relation arguments; it is an input relation, not an unproved global
    dependency. *)
Lemma monotone_correspondence_certificate :
  forall (T : Type)
         (RR : T -> T -> bool)
         (RL : T -> T -> ImportedRel.Bool)
         (f : T -> T),
    (forall x y,
      PropSPropRel
        (is_true (RR x y))
        (Lean.eq (RL x y) ImportedRel.Bool_true)) ->
    PropSPropRel
      (@prosa.util.rel.monotone T RR f)
      (Prosa_Util_Rel_monotone T RL f).
Proof.
  intros T RR RL f HR.
  constructor.
  - intros H x y Hxy.
    apply (prop_to_sprop _ _ (HR (f x) (f y))).
    apply H.
    exact (sprop_to_prop _ _ (HR x y) Hxy).
  - intros H x y Hxy.
    apply (sprop_to_prop _ _ (HR (f x) (f y))).
    apply H.
    exact (prop_to_sprop _ _ (HR x y) Hxy).
Qed.
