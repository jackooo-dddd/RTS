From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedNat.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  NatSubCorrespondence.
From prosa Require Import util.nat.

Definition rocq_subnACA_at (m n p q : nat) : Prop :=
  is_true (leq p m) ->
  is_true (leq q n) ->
  Logic.eq ((m + n) - (p + q)) ((m - p) + (n - q)).

Definition imported_subnACA_at (m n p q : Lean.Nat) : SProp :=
  nat_target_le p m ->
  nat_target_le q n ->
  Lean.eq
    (nat_target_sub (nat_target_add m n) (nat_target_add p q))
    (nat_target_add (nat_target_sub m p) (nat_target_sub n q)).

Definition rocq_subnACA_type_guard :
  forall m n p q : nat, rocq_subnACA_at m n p q :=
  @prosa.util.nat.subnACA.

Definition imported_subnACA_type_guard :
  forall m n p q : Lean.Nat, imported_subnACA_at m n p q :=
  @ImportedNat.Prosa_Util_Nat_subnACA.

Lemma subnACA_correspondence_certificate :
  forall mR mL nR nL pR pL qR qL,
    SubNatRel mR mL -> SubNatRel nR nL ->
    SubNatRel pR pL -> SubNatRel qR qL ->
    PropSPropRel
      (rocq_subnACA_at mR nR pR qR)
      (imported_subnACA_at mL nL pL qL).
Proof.
  intros mR mL nR nL pR pL qR qL Hm Hn Hp Hq.
  apply prop_sprop_rel_intro.
  - intros Hsource HpmL HqnL.
    have HpmR := sprop_to_prop _ _
      (nat_target_le_correspondence _ _ _ _ Hp Hm) HpmL.
    have HqnR := sprop_to_prop _ _
      (nat_target_le_correspondence _ _ _ _ Hq Hn) HqnL.
    have HsourceEq := Hsource HpmR HqnR.
    have Hmn := nat_target_add_correspondence _ _ _ _ Hm Hn.
    have Hpq := nat_target_add_correspondence _ _ _ _ Hp Hq.
    have Hleft := nat_target_sub_correspondence _ _ _ _ Hmn Hpq.
    have Hmp := nat_target_sub_correspondence _ _ _ _ Hm Hp.
    have Hnq := nat_target_sub_correspondence _ _ _ _ Hn Hq.
    have Hright := nat_target_add_correspondence _ _ _ _ Hmp Hnq.
    exact (prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hleft Hright) HsourceEq).
  - intro Htarget. apply strictly_inhabits. intros HpmR HqnR.
    have HpmL := prop_to_sprop _ _
      (nat_target_le_correspondence _ _ _ _ Hp Hm) HpmR.
    have HqnL := prop_to_sprop _ _
      (nat_target_le_correspondence _ _ _ _ Hq Hn) HqnR.
    have HtargetEq := Htarget HpmL HqnL.
    have Hmn := nat_target_add_correspondence _ _ _ _ Hm Hn.
    have Hpq := nat_target_add_correspondence _ _ _ _ Hp Hq.
    have Hleft := nat_target_sub_correspondence _ _ _ _ Hmn Hpq.
    have Hmp := nat_target_sub_correspondence _ _ _ _ Hm Hp.
    have Hnq := nat_target_sub_correspondence _ _ _ _ Hn Hq.
    have Hright := nat_target_add_correspondence _ _ _ _ Hmp Hnq.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hleft Hright) HtargetEq).
Qed.

Definition rocq_leq_subRL_impl_at (m n p : nat) : Prop :=
  is_true (leq (m + n) p) -> is_true (leq n (p - m)).

Definition imported_leq_subRL_impl_at (m n p : Lean.Nat) : SProp :=
  nat_target_le (nat_target_add m n) p ->
  nat_target_le n (nat_target_sub p m).

Definition rocq_leq_subRL_impl_type_guard :
  forall m n p : nat, rocq_leq_subRL_impl_at m n p :=
  @prosa.util.nat.leq_subRL_impl.

Definition imported_leq_subRL_impl_type_guard :
  forall m n p : Lean.Nat, imported_leq_subRL_impl_at m n p :=
  @ImportedNat.Prosa_Util_Nat_leq_subRL_impl.

Lemma leq_subRL_impl_correspondence_certificate :
  forall mR mL nR nL pR pL,
    SubNatRel mR mL -> SubNatRel nR nL -> SubNatRel pR pL ->
    PropSPropRel
      (rocq_leq_subRL_impl_at mR nR pR)
      (imported_leq_subRL_impl_at mL nL pL).
Proof.
  intros mR mL nR nL pR pL Hm Hn Hp.
  apply prop_sprop_rel_intro.
  - intros Hsource HsumL.
    have Hmn := nat_target_add_correspondence _ _ _ _ Hm Hn.
    have HsumR := sprop_to_prop _ _
      (nat_target_le_correspondence _ _ _ _ Hmn Hp) HsumL.
    have HresultR := Hsource HsumR.
    have Hpm := nat_target_sub_correspondence _ _ _ _ Hp Hm.
    exact (prop_to_sprop _ _
      (nat_target_le_correspondence _ _ _ _ Hn Hpm) HresultR).
  - intro Htarget. apply strictly_inhabits. intro HsumR.
    have Hmn := nat_target_add_correspondence _ _ _ _ Hm Hn.
    have HsumL := prop_to_sprop _ _
      (nat_target_le_correspondence _ _ _ _ Hmn Hp) HsumR.
    have HresultL := Htarget HsumL.
    have Hpm := nat_target_sub_correspondence _ _ _ _ Hp Hm.
    exact (sprop_to_prop _ _
      (nat_target_le_correspondence _ _ _ _ Hn Hpm) HresultL).
Qed.

Print Assumptions subnACA_correspondence_certificate.
Print Assumptions leq_subRL_impl_correspondence_certificate.
