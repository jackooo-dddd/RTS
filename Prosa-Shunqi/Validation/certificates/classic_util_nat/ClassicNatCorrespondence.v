From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From prosa Require Import classic.util.nat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicNat.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicNatBase.

Module I := ImportedClassicNat.
Local Open Scope nat_scope.

(** Certificates for [classic/util/nat.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: natural numbers by the accepted [SubNatRel], Booleans
    constructor-wise (two-way totals).  Arithmetic: addition by the accepted
    [sub_add_correspondence]; truncated subtraction and [minn] by structural
    computation of the Lean operations ([ClassicNatBase]); Lean decisions are
    never unfolded.  Statements: the source side is the exact elaborated type
    of the pinned lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma cn_iff (P Q : Prop) (PL QL : SProp) :
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

Notation cn_add := sub_add_correspondence.

Definition src_subh1 : Prop := ltac:(type_of_term @subh1).
Definition tgt_subh1 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Nat_subh1).
Theorem subh1_correspondence : PropSPropRel src_subh1 tgt_subh1.
Proof.
  unfold src_subh1, tgt_subh1.
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => p pL Hp.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hn Hm).
  exact (sub_nat_eq_correspondence _ _ _ _ (cn_add _ _ _ _ (ct_sub_rel _ _ _ _ Hm Hn) Hp)
           (ct_sub_rel _ _ _ _ (cn_add _ _ _ _ Hm Hp) Hn)).
Qed.

Definition src_subh2 : Prop := ltac:(type_of_term @subh2).
Definition tgt_subh2 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Nat_subh2).
Theorem subh2_correspondence : PropSPropRel src_subh2 tgt_subh2.
Proof.
  unfold src_subh2, tgt_subh2.
  apply: ct_forall_nat => m1 m1L H1. apply: ct_forall_nat => m2 m2L H2.
  apply: ct_forall_nat => n1 n1L H3. apply: ct_forall_nat => n2 n2L H4.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 H1).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H4 H3).
  exact (sub_nat_eq_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cn_add _ _ _ _ H1 H3) (cn_add _ _ _ _ H2 H4))
           (cn_add _ _ _ _ (ct_sub_rel _ _ _ _ H1 H2) (ct_sub_rel _ _ _ _ H3 H4))).
Qed.

Definition src_addnb : Prop := ltac:(type_of_term @addnb).
Definition tgt_addnb : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Nat_addnb).
Theorem addnb_correspondence : PropSPropRel src_addnb tgt_addnb.
Proof.
  unfold src_addnb, tgt_addnb.
  apply: ct_forall_bool => b1 b1L H1. apply: ct_forall_bool => b2 b2L H2.
  apply: ct_bool_eq; last exact (ct_bool_or _ _ _ _ H1 H2).
  apply: ct_bool_not. apply: ct_decide_eq_nat; last exact (sub_nat_rel_canonical 0).
  exact (cn_add _ _ _ _ (ct_bool_to_nat _ _ H1) (ct_bool_to_nat _ _ H2)).
Qed.

Definition src_subh4 : Prop := ltac:(type_of_term @subh4).
Definition tgt_subh4 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Nat_subh4).
Theorem subh4_correspondence : PropSPropRel src_subh4 tgt_subh4.
Proof.
  unfold src_subh4, tgt_subh4.
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => p pL Hp.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hm Hn).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hp Hn).
  exact (ct_bool_eq _ _ _ _ (ct_decide_eq_nat _ _ _ _ Hm (ct_sub_rel _ _ _ _ Hn Hp))
           (ct_decide_eq_nat _ _ _ _ Hp (ct_sub_rel _ _ _ _ Hn Hm))).
Qed.

Definition src_addmovr : Prop := ltac:(type_of_term @addmovr).
Definition tgt_addmovr : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Nat_addmovr).
Theorem addmovr_correspondence : PropSPropRel src_addmovr tgt_addmovr.
Proof.
  unfold src_addmovr, tgt_addmovr.
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => p pL Hp.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hn Hm).
  exact (cn_iff _ _ _ _ (sub_nat_eq_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ Hm Hn) Hp)
           (sub_nat_eq_correspondence _ _ _ _ Hm (cn_add _ _ _ _ Hp Hn))).
Qed.

Definition src_addmovl : Prop := ltac:(type_of_term @addmovl).
Definition tgt_addmovl : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Nat_addmovl).
Theorem addmovl_correspondence : PropSPropRel src_addmovl tgt_addmovl.
Proof.
  unfold src_addmovl, tgt_addmovl.
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => p pL Hp.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hn Hm).
  exact (cn_iff _ _ _ _ (sub_nat_eq_correspondence _ _ _ _ Hp (ct_sub_rel _ _ _ _ Hm Hn))
           (sub_nat_eq_correspondence _ _ _ _ (cn_add _ _ _ _ Hp Hn) Hm)).
Qed.

Lemma cn_succ nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                    (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro H. have := cn_add _ _ 1 _ H (sub_nat_rel_canonical 1). by rewrite addn1. Qed.

Definition src_ltSnm : Prop := ltac:(type_of_term @ltSnm).
Definition tgt_ltSnm : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Nat_ltSnm).
Theorem ltSnm_correspondence : PropSPropRel src_ltSnm tgt_ltSnm.
Proof.
  unfold src_ltSnm, tgt_ltSnm.
  apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => m mL Hm.
  exact (ct_imp _ _ _ _ (sub_nat_lt_correspondence _ _ _ _ (cn_succ _ _ Hn) Hm) (sub_nat_lt_correspondence _ _ _ _ Hn Hm)).
Qed.

Definition src_min_lt_same : Prop := ltac:(type_of_term @min_lt_same).
Definition tgt_min_lt_same : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Nat_min_lt_same).
Theorem min_lt_same_correspondence : PropSPropRel src_min_lt_same tgt_min_lt_same.
Proof.
  unfold src_min_lt_same, tgt_min_lt_same.
  apply: ct_forall_nat => x xL Hx. apply: ct_forall_nat => y yL Hy. apply: ct_forall_nat => z zL Hz.
  exact (ct_imp _ _ _ _ (sub_nat_lt_correspondence _ _ _ _ (ct_min_rel _ _ _ _ Hx Hz) (ct_min_rel _ _ _ _ Hy Hz))
           (sub_nat_lt_correspondence _ _ _ _ Hx Hy)).
Qed.
