From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSuperadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
Require Import GeneratedSuperadditivitySourceBase.

(** The source bodies above are byte-identical computational declarations
    extracted from pinned v0.6; the target bodies are the actual compiled
    Lean definitions imported from Superadditivity.out. *)

Lemma superadditive_at_correspondence :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall hR hL, SubNatRel hR hL ->
    PropSPropRel
      (GeneratedSuperadditivitySourceBase.superadditive_at fR hR)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_at fL hL).
Proof.
  intros fR fL Hf hR hL Hh. apply prop_sprop_rel_intro.
  - intros Hsource aL bL HsumL.
    set (aR := sub_nat_to_rocq aL).
    set (bR := sub_nat_to_rocq bL).
    have Ha : SubNatRel aR aL := sub_nat_rel_surjective aL.
    have Hb : SubNatRel bR bL := sub_nat_rel_surjective bL.
    have HsumRel := sub_add_correspondence aR aL bR bL Ha Hb.
    have HsumR := sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _ HsumRel Hh) HsumL.
    have HleR := Hsource aR bR HsumR.
    have Hfh := Hf hR hL Hh.
    have Hfa := Hf aR aL Ha.
    have Hfb := Hf bR bL Hb.
    have HaddF := sub_add_correspondence _ _ _ _ Hfa Hfb.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ HaddF Hfh) HleR).
  - intro Htarget. apply strictly_inhabits.
    intros aR bR HsumR.
    have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have HsumRel := sub_add_correspondence _ _ _ _ Ha Hb.
    have HsumL := prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ HsumRel Hh) HsumR.
    have HleL := Htarget _ _ HsumL.
    have Hfh := Hf hR hL Hh.
    have Hfa := Hf _ _ Ha.
    have Hfb := Hf _ _ Hb.
    have HaddF := sub_add_correspondence _ _ _ _ Hfa Hfb.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ HaddF Hfh) HleL).
Qed.

Lemma superadditive_until_correspondence :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall hR hL, SubNatRel hR hL ->
    PropSPropRel
      (GeneratedSuperadditivitySourceBase.superadditive_until fR hR)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_until fL hL).
Proof.
  intros fR fL Hf hR hL Hh. apply prop_sprop_rel_intro.
  - intros Hsource xL HltL.
    set (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have HltR := sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Hh) HltL.
    exact (prop_to_sprop _ _
      (superadditive_at_correspondence fR fL Hf xR xL Hx)
      (Hsource xR HltR)).
  - intro Htarget. apply strictly_inhabits.
    intros xR HltR.
    have Hx := sub_nat_rel_canonical xR.
    have HltL := prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Hh) HltR.
    exact (sprop_to_prop _ _
      (superadditive_at_correspondence fR fL Hf _ _ Hx)
      (Htarget _ HltL)).
Qed.

Lemma superadditive_correspondence :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (GeneratedSuperadditivitySourceBase.superadditive fR)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL).
Proof.
  intros fR fL Hf. apply prop_sprop_rel_intro.
  - intros Hsource hL.
    set (hR := sub_nat_to_rocq hL).
    have Hh : SubNatRel hR hL := sub_nat_rel_surjective hL.
    exact (prop_to_sprop _ _
      (superadditive_at_correspondence fR fL Hf hR hL Hh)
      (Hsource hR)).
  - intro Htarget. apply strictly_inhabits.
    intro hR. have Hh := sub_nat_rel_canonical hR.
    exact (sprop_to_prop _ _
      (superadditive_at_correspondence fR fL Hf _ _ Hh)
      (Htarget _)).
Qed.

Lemma superadditive_standard_correspondence :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (GeneratedSuperadditivitySourceBase.superadditive_standard fR)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_standard fL).
Proof.
  intros fR fL Hf. apply prop_sprop_rel_intro.
  - intros Hsource aL bL.
    set (aR := sub_nat_to_rocq aL).
    set (bR := sub_nat_to_rocq bL).
    have Ha : SubNatRel aR aL := sub_nat_rel_surjective aL.
    have Hb : SubNatRel bR bL := sub_nat_rel_surjective bL.
    have Hab := sub_add_correspondence _ _ _ _ Ha Hb.
    have Hfab := Hf _ _ Hab.
    have Hfa := Hf _ _ Ha.
    have Hfb := Hf _ _ Hb.
    have HaddF := sub_add_correspondence _ _ _ _ Hfa Hfb.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ HaddF Hfab)
      (Hsource aR bR)).
  - intro Htarget. apply strictly_inhabits.
    intros aR bR.
    have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have Hab := sub_add_correspondence _ _ _ _ Ha Hb.
    have Hfab := Hf _ _ Hab.
    have Hfa := Hf _ _ Ha.
    have Hfb := Hf _ _ Hb.
    have HaddF := sub_add_correspondence _ _ _ _ Hfa Hfb.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ HaddF Hfab)
      (Htarget _ _)).
Qed.

Print Assumptions superadditive_at_correspondence.
Print Assumptions superadditive_until_correspondence.
Print Assumptions superadditive_correspondence.
Print Assumptions superadditive_standard_correspondence.
