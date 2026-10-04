From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From prosa Require Import classic.util.induction.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicInduction.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.

Module I := ImportedClassicInduction.

(** Certificates for [classic/util/induction.v] (ProsaBuddy classic, commit f692cb7).

    Inputs.  Natural numbers by the accepted [SubNatRel]; predicates
    [nat -> Prop] against Lean's [Nat -> Prop] (imported as [Nat -> SProp])
    pointwise by [PropSPropRel] ([CiPropPredRel]); both relations have two-way
    totals (the predicate cover uses [StrictlyInhabited] and the box [CiBox]).

    Statements.  The source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma ci_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma ci_imp (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ). exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ). exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma ci_iff (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [f g]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (f (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (g (sprop_to_prop _ _ HQ q))).
  - intros [f g]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (f (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (g (prop_to_sprop _ _ HQ q))).
Qed.

Lemma ci_forall_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall n, PR n) (forall n, PL n).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _ (H _ _ (sub_nat_rel_surjective nL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro nR. exact (sprop_to_prop _ _ (H _ _ (sub_nat_rel_canonical nR)) (HL _)).
Qed.

Definition CiPropPredRel (PR : nat -> Prop) (PL : Lean.Nat -> SProp) : Prop :=
  forall kR kL, SubNatRel kR kL -> PropSPropRel (PR kR) (PL kL).

Inductive CiBox (Q : SProp) : Prop := ci_box : Q -> CiBox Q.

Lemma ci_box_rel (Q : SProp) : PropSPropRel (CiBox Q) Q.
Proof.
  apply prop_sprop_rel_intro.
  - intros [q]. exact q.
  - intro q. apply strictly_inhabits. exact (ci_box Q q).
Qed.

Lemma ci_strict_rel (P : Prop) : PropSPropRel P (StrictlyInhabited P).
Proof.
  apply prop_sprop_rel_intro.
  - intro p. exact (strictly_inhabits p).
  - intro p. exact p.
Qed.

Lemma ci_forall_prop_pred (PR : (nat -> Prop) -> Prop) (PL : (Lean.Nat -> SProp) -> SProp) :
  (forall PRp PLp, CiPropPredRel PRp PLp -> PropSPropRel (PR PRp) (PL PLp)) ->
  PropSPropRel (forall P, PR P) (forall P, PL P).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR PLp.
    have Hrel : CiPropPredRel (fun kR => CiBox (PLp (sub_nat_to_imported kR))) PLp.
    { intros kR kL Hk. have E := ci_nat_logic _ _ Hk. subst kL. exact (ci_box_rel _). }
    exact (prop_to_sprop _ _ (H _ _ Hrel) (HR _)).
  - intro HL. apply strictly_inhabits. intro PRp.
    have Hrel : CiPropPredRel PRp (fun kL => StrictlyInhabited (PRp (sub_nat_to_rocq kL))).
    { intros kR kL Hk. have E := ci_nat_logic _ _ Hk. subst kL.
      rewrite sub_nat_rocq_roundtrip. exact (ci_strict_rel _). }
    exact (sprop_to_prop _ _ (H _ _ Hrel) (HL _)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_strong_ind : Prop := ltac:(type_of_term @strong_ind).
Definition tgt_strong_ind : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Induction_strong_ind).
Theorem strong_ind_correspondence : PropSPropRel src_strong_ind tgt_strong_ind.
Proof.
  unfold src_strong_ind, tgt_strong_ind.
  apply: ci_forall_prop_pred => PR PL HP.
  apply: ci_imp.
  - apply: ci_forall_nat => nR nL Hn. apply: ci_imp; last exact (HP _ _ Hn).
    apply: ci_forall_nat => kR kL Hk.
    exact (ci_imp _ _ _ _ (sub_nat_lt_correspondence _ _ _ _ Hk Hn) (HP _ _ Hk)).
  - apply: ci_forall_nat => nR nL Hn. exact (HP _ _ Hn).
Qed.

Definition src_leq_as_delta : Prop := ltac:(type_of_term @leq_as_delta).
Definition tgt_leq_as_delta : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Induction_leq_as_delta).
Theorem leq_as_delta_correspondence : PropSPropRel src_leq_as_delta tgt_leq_as_delta.
Proof.
  unfold src_leq_as_delta, tgt_leq_as_delta.
  apply: ci_forall_nat => x1R x1L H1. apply: ci_forall_prop_pred => PR PL HP.
  apply: ci_iff.
  - apply: ci_forall_nat => x2R x2L H2.
    exact (ci_imp _ _ _ _ (sub_nat_le_correspondence _ _ _ _ H1 H2) (HP _ _ H2)).
  - apply: ci_forall_nat => dR dL Hd. exact (HP _ _ (sub_add_correspondence _ _ _ _ H1 Hd)).
Qed.
