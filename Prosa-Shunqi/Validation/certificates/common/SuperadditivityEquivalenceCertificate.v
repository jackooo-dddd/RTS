From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSuperadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence SuperadditivityBaseCorrespondence.
Require Import OfficialSuperadditivityEquiv.

Definition superadditivity_equivalence_target_statement : SProp :=
  forall fL : Lean.Nat -> Lean.Nat,
    ImportedSuperadditivity.Iff
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_standard fL).

Lemma superadditivity_pullback_related (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel
    (fun nR => sub_nat_to_rocq (fL (sub_nat_to_imported nR))) fL.
Proof.
  intros nR nL Hn. unfold SubNatRel in *.
  exact (sub_imported_eq_trans _ _ _
    (sub_nat_rel_surjective _)
    (sub_imported_eq_congr fL _ _ Hn)).
Qed.

Lemma superadditivity_pushforward_related (fR : nat -> nat) :
  SubNatFunRel fR
    (fun nL => sub_nat_to_imported (fR (sub_nat_to_rocq nL))).
Proof.
  intros nR nL Hn. unfold SubNatRel in *.
  have Hnr := imported_eq_to_coq_eq _ _ Hn.
  have Hnr' : Logic.eq nR (sub_nat_to_rocq nL).
  { rewrite -Hnr. rewrite sub_nat_rocq_roundtrip. reflexivity. }
  rewrite -Hnr'. exact (sub_nat_rel_canonical (fR nR)).
Qed.

(** The exact target theorem constant appears only in a separate type guard,
    never in the correspondence proof below. *)
Lemma superadditivity_equivalence_statement_certificate :
  PropSPropRel
    OfficialSuperadditivityEquiv.statement_superadditive_standard_equivalence
    superadditivity_equivalence_target_statement.
Proof.
  apply prop_sprop_rel_intro.
  - intros Hsource fL.
    set (fR := fun nR : nat =>
      sub_nat_to_rocq (fL (sub_nat_to_imported nR))).
    pose (Hf := superadditivity_pullback_related fL).
    have Hleft : PropSPropRel
      (OfficialSuperadditivityEquiv.superadditive fR)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL).
    { exact (superadditive_correspondence fR fL Hf). }
    have Hright : PropSPropRel
      (OfficialSuperadditivityEquiv.superadditive_standard fR)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_standard fL).
    { exact (superadditive_standard_correspondence fR fL Hf). }
    apply ImportedSuperadditivity.Iff_intro.
    + intro HleftL.
      exact (prop_to_sprop _ _ Hright
        (proj1 (Hsource fR) (sprop_to_prop _ _ Hleft HleftL))).
    + intro HrightL.
      exact (prop_to_sprop _ _ Hleft
        (proj2 (Hsource fR) (sprop_to_prop _ _ Hright HrightL))).
  - intro Htarget. apply strictly_inhabits. intro fR.
    set (fL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fR (sub_nat_to_rocq nL))).
    pose (Hf := superadditivity_pushforward_related fR).
    have Hleft : PropSPropRel
      (OfficialSuperadditivityEquiv.superadditive fR)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL).
    { exact (superadditive_correspondence fR fL Hf). }
    have Hright : PropSPropRel
      (OfficialSuperadditivityEquiv.superadditive_standard fR)
      (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_standard fL).
    { exact (superadditive_standard_correspondence fR fL Hf). }
    split.
    + intro HleftR.
      exact (sprop_to_prop _ _ Hright
        (ImportedSuperadditivity.mp _ _ (Htarget fL)
          (prop_to_sprop _ _ Hleft HleftR))).
    + intro HrightR.
      exact (sprop_to_prop _ _ Hleft
        (ImportedSuperadditivity.mpr _ _ (Htarget fL)
          (prop_to_sprop _ _ Hright HrightR))).
Qed.

Print Assumptions superadditivity_equivalence_statement_certificate.
