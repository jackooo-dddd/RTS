From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpace.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

Lemma ss_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (Lean.And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (Lean.And_intro PL QL
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intro H. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP (ImportedSearchSpace.And_left _ _ H)).
    + exact (sprop_to_prop _ _ HQ (ImportedSearchSpace.And_right _ _ H)).
Qed.

Lemma ss_andb_elim (p q : bool) :
  is_true (andb p q) -> is_true p /\ is_true q.
Proof. move=> /andP [Hp Hq]. split; assumption. Qed.

Lemma ss_andb_intro (p q : bool) :
  is_true p -> is_true q -> is_true (andb p q).
Proof. move=> Hp Hq. apply/andP. split; assumption. Qed.

Lemma ss_andb_correspondence (p q : bool) (PL QL : SProp) :
  PropSPropRel (is_true p) PL -> PropSPropRel (is_true q) QL ->
  PropSPropRel (is_true (andb p q)) (Lean.And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intro H. destruct (ss_andb_elim p q H) as [Hp Hq].
    exact (Lean.And_intro PL QL
      (prop_to_sprop _ _ HP Hp) (prop_to_sprop _ _ HQ Hq)).
  - intro H. apply strictly_inhabits.
    exact (ss_andb_intro p q
      (sprop_to_prop _ _ HP (ImportedSearchSpace.And_left _ _ H))
      (sprop_to_prop _ _ HQ (ImportedSearchSpace.And_right _ _ H))).
Qed.

Lemma ss_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p | q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p | q].
    + exact (strictly_inhabits (or_introl (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror (sprop_to_prop _ _ HQ q))).
Qed.

Lemma ss_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H pL. exact (prop_to_sprop _ _ HQ
      (H (sprop_to_prop _ _ HP pL))).
  - intro H. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ HQ
      (H (prop_to_sprop _ _ HP pR))).
Qed.

Lemma ss_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall xR xL, SubNatRel xR xL ->
    PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (exists xR, PR xR)
    (ImportedSearchSpace.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [xR Hx].
    apply (ImportedSearchSpace.Exists_intro _ _ (sub_nat_to_imported xR)).
    exact (prop_to_sprop _ _
      (HP xR (sub_nat_to_imported xR) (sub_nat_rel_canonical xR)) Hx).
  - intro H. destruct H as [xL Hx].
    apply strictly_inhabits. exists (sub_nat_to_rocq xL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq xL) xL (sub_nat_rel_surjective xL)) Hx).
Qed.

Lemma ss_forall_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall xR xL, SubNatRel xR xL ->
    PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (forall xR, PR xR) (forall xL, PL xL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR xL. exact (prop_to_sprop _ _
      (HP (sub_nat_to_rocq xL) xL (sub_nat_rel_surjective xL))
      (HR (sub_nat_to_rocq xL))).
  - intro HL. apply strictly_inhabits. intro xR.
    exact (sprop_to_prop _ _
      (HP xR (sub_nat_to_imported xR) (sub_nat_rel_canonical xR))
      (HL (sub_nat_to_imported xR))).
Qed.

Print Assumptions ss_and_correspondence.
Print Assumptions ss_andb_correspondence.
Print Assumptions ss_or_correspondence.
Print Assumptions ss_imp_correspondence.
Print Assumptions ss_exists_nat_correspondence.
Print Assumptions ss_forall_nat_correspondence.
