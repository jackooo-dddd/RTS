From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSuperadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence SuperadditivityBaseCorrespondence
  SuperadditivityEquivalenceCertificate SuperadditivityExtensionOperations.
Require Import OfficialSuperadditivityHorizon.

Definition sa_source_update (f : nat -> nat) (h t : nat) : nat :=
  if t == h then
    OfficialSuperadditivityHorizon.minimal_superadditive_extension f h
  else f t.

Lemma sa_update_hyp_related fR fL hR hL fpR fpL :
  SubNatFunRel fR fL -> SubNatRel hR hL -> SubNatFunRel fpR fpL ->
  PropSPropRel
    (forall tR, Logic.eq (fpR tR) (sa_source_update fR hR tR))
    (forall tL, Lean.eq (fpL tL) (sa_target_update fL hL tL)).
Proof.
  intros Hf Hh Hfp. apply prop_sprop_rel_intro.
  - intros HR tL.
    set (tR := sub_nat_to_rocq tL).
    have Ht : SubNatRel tR tL := sub_nat_rel_surjective tL.
    have Hfpv := Hfp tR tL Ht.
    have Hupdate := sa_update_related fR fL hR hL tR tL Hf Hh Ht.
    exact (prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hfpv Hupdate) (HR tR)).
  - intro HL. apply strictly_inhabits. intro tR.
    have Ht := sub_nat_rel_canonical tR.
    have Hfpv := Hfp tR _ Ht.
    have Hupdate := sa_update_related fR fL hR hL tR _ Hf Hh Ht.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hfpv Hupdate) (HL _)).
Qed.

Definition sa_horizon_at_target_statement : SProp :=
  forall (fL : Lean.Nat -> Lean.Nat) (hL : Lean.Nat),
    ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_until fL hL ->
    forall fpL : Lean.Nat -> Lean.Nat,
      (forall tL, Lean.eq (fpL tL) (sa_target_update fL hL tL)) ->
      ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_at fpL hL.

Lemma sa_horizon_at_statement_certificate :
  PropSPropRel
    OfficialSuperadditivityHorizon.statement_minimal_extension_superadditive_at_horizon
    sa_horizon_at_target_statement.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL HuntilL fpL HupdateL.
    set (fR := fun nR : nat =>
      sub_nat_to_rocq (fL (sub_nat_to_imported nR))).
    set (hR := sub_nat_to_rocq hL).
    set (fpR := fun nR : nat =>
      sub_nat_to_rocq (fpL (sub_nat_to_imported nR))).
    have Hf := superadditivity_pullback_related fL.
    have Hh : SubNatRel hR hL := sub_nat_rel_surjective hL.
    have Hfp := superadditivity_pullback_related fpL.
    have HuntilR := sprop_to_prop _ _
      (superadditive_until_correspondence fR fL Hf hR hL Hh) HuntilL.
    have HupdateR := sprop_to_prop _ _
      (sa_update_hyp_related fR fL hR hL fpR fpL Hf Hh Hfp) HupdateL.
    exact (prop_to_sprop _ _
      (superadditive_at_correspondence fpR fpL Hfp hR hL Hh)
      (HR fR hR HuntilR fpR HupdateR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR HuntilR fpR HupdateR.
    set (fL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fR (sub_nat_to_rocq nL))).
    set (hL := sub_nat_to_imported hR).
    set (fpL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fpR (sub_nat_to_rocq nL))).
    have Hf := superadditivity_pushforward_related fR.
    have Hh : SubNatRel hR hL := sub_nat_rel_canonical hR.
    have Hfp := superadditivity_pushforward_related fpR.
    have HuntilL := prop_to_sprop _ _
      (superadditive_until_correspondence fR fL Hf hR hL Hh) HuntilR.
    have HupdateL := prop_to_sprop _ _
      (sa_update_hyp_related fR fL hR hL fpR fpL Hf Hh Hfp) HupdateR.
    exact (sprop_to_prop _ _
      (superadditive_at_correspondence fpR fpL Hfp hR hL Hh)
      (HL fL hL HuntilL fpL HupdateL)).
Qed.

Definition sa_target_horizon_succ (hL : Lean.Nat) : Lean.Nat :=
  sa_target_add hL sa_target_one.

Lemma sa_horizon_succ_related hR hL :
  SubNatRel hR hL -> SubNatRel hR.+1 (sa_target_horizon_succ hL).
Proof.
  intro Hh. rewrite -addn1.
  exact (sa_add_related hR hL 1 sa_target_one Hh
    (sub_nat_rel_canonical 1)).
Qed.

Definition sa_horizon_until_target_statement : SProp :=
  forall (fL : Lean.Nat -> Lean.Nat) (hL : Lean.Nat),
    ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_until fL hL ->
    forall fpL : Lean.Nat -> Lean.Nat,
      (forall tL, Lean.eq (fpL tL) (sa_target_update fL hL tL)) ->
      ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_until
        fpL (sa_target_horizon_succ hL).

Lemma sa_horizon_until_statement_certificate :
  PropSPropRel
    OfficialSuperadditivityHorizon.statement_minimal_extension_superadditive_until
    sa_horizon_until_target_statement.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL HuntilL fpL HupdateL.
    set (fR := fun nR : nat =>
      sub_nat_to_rocq (fL (sub_nat_to_imported nR))).
    set (hR := sub_nat_to_rocq hL).
    set (fpR := fun nR : nat =>
      sub_nat_to_rocq (fpL (sub_nat_to_imported nR))).
    have Hf := superadditivity_pullback_related fL.
    have Hh : SubNatRel hR hL := sub_nat_rel_surjective hL.
    have Hfp := superadditivity_pullback_related fpL.
    have HuntilR := sprop_to_prop _ _
      (superadditive_until_correspondence fR fL Hf hR hL Hh) HuntilL.
    have HupdateR := sprop_to_prop _ _
      (sa_update_hyp_related fR fL hR hL fpR fpL Hf Hh Hfp) HupdateL.
    have Hsucc := sa_horizon_succ_related hR hL Hh.
    exact (prop_to_sprop _ _
      (superadditive_until_correspondence fpR fpL Hfp _ _ Hsucc)
      (HR fR hR HuntilR fpR HupdateR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR HuntilR fpR HupdateR.
    set (fL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fR (sub_nat_to_rocq nL))).
    set (hL := sub_nat_to_imported hR).
    set (fpL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fpR (sub_nat_to_rocq nL))).
    have Hf := superadditivity_pushforward_related fR.
    have Hh : SubNatRel hR hL := sub_nat_rel_canonical hR.
    have Hfp := superadditivity_pushforward_related fpR.
    have HuntilL := prop_to_sprop _ _
      (superadditive_until_correspondence fR fL Hf hR hL Hh) HuntilR.
    have HupdateL := prop_to_sprop _ _
      (sa_update_hyp_related fR fL hR hL fpR fpL Hf Hh Hfp) HupdateR.
    have Hsucc := sa_horizon_succ_related hR hL Hh.
    exact (sprop_to_prop _ _
      (superadditive_until_correspondence fpR fpL Hfp _ _ Hsucc)
      (HL fL hL HuntilL fpL HupdateL)).
Qed.

Print Assumptions sa_update_hyp_related.
Print Assumptions sa_horizon_at_statement_certificate.
Print Assumptions sa_horizon_until_statement_certificate.
