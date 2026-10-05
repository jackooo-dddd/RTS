From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSuperadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence SuperadditivityBaseCorrespondence
  SuperadditivityEquivalenceCertificate.
Require Import OfficialSuperadditivityArithmetic.

Definition superadditivity_target_zero : Lean.Nat :=
  ImportedSuperadditivity.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedSuperadditivity.instOfNatNat Lean.Nat_zero).

Definition superadditivity_first_zero_target_statement : SProp :=
  forall fL : Lean.Nat -> Lean.Nat,
    ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_at
      fL superadditivity_target_zero ->
    Lean.eq (fL superadditivity_target_zero) superadditivity_target_zero.

Lemma superadditivity_first_zero_related
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (Hf : SubNatFunRel fR fL) :
  PropSPropRel
    (OfficialSuperadditivityArithmetic.superadditive_at fR O ->
      Logic.eq (fR O) O)
    (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_at
      fL superadditivity_target_zero ->
      Lean.eq (fL superadditivity_target_zero)
        superadditivity_target_zero).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR HatL.
    have Hzero : SubNatRel O superadditivity_target_zero :=
      sub_nat_rel_canonical O.
    have HatR := sprop_to_prop _ _
      (superadditive_at_correspondence fR fL Hf _ _ Hzero) HatL.
    exact (prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ (Hf _ _ Hzero) Hzero)
      (HR HatR)).
  - intro HL. apply strictly_inhabits. intro HatR.
    have Hzero : SubNatRel O superadditivity_target_zero :=
      sub_nat_rel_canonical O.
    have HatL := prop_to_sprop _ _
      (superadditive_at_correspondence fR fL Hf _ _ Hzero) HatR.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _ (Hf _ _ Hzero) Hzero)
      (HL HatL)).
Qed.

Lemma superadditivity_first_zero_statement_certificate :
  PropSPropRel
    OfficialSuperadditivityArithmetic.statement_superadditive_first_zero
    superadditivity_first_zero_target_statement.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL.
    set (fR := fun nR : nat =>
      sub_nat_to_rocq (fL (sub_nat_to_imported nR))).
    pose (Hf := superadditivity_pullback_related fL).
    exact (prop_to_sprop _ _
      (superadditivity_first_zero_related fR fL Hf) (HR fR)).
  - intro HL. apply strictly_inhabits. intro fR.
    set (fL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fR (sub_nat_to_rocq nL))).
    pose (Hf := superadditivity_pushforward_related fR).
    exact (sprop_to_prop _ _
      (superadditivity_first_zero_related fR fL Hf) (HL fL)).
Qed.

Definition superadditivity_leq_mul_target_statement : SProp :=
  forall fL : Lean.Nat -> Lean.Nat,
    ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL ->
    forall nL mL : Lean.Nat,
      sub_imported_le (sub_imported_mul mL (fL nL))
        (fL (sub_imported_mul mL nL)).

Lemma superadditivity_leq_mul_related
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (Hf : SubNatFunRel fR fL) :
  PropSPropRel
    (OfficialSuperadditivityArithmetic.superadditive fR ->
      forall nR mR : nat,
        is_true (leq (mR * fR nR) (fR (mR * nR))))
    (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL ->
      forall nL mL : Lean.Nat,
        sub_imported_le (sub_imported_mul mL (fL nL))
          (fL (sub_imported_mul mL nL))).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR HsuperL nL mL.
    set (nR := sub_nat_to_rocq nL).
    set (mR := sub_nat_to_rocq mL).
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hm : SubNatRel mR mL := sub_nat_rel_surjective mL.
    have HsuperR := sprop_to_prop _ _
      (superadditive_correspondence fR fL Hf) HsuperL.
    have Hfn := Hf nR nL Hn.
    have Hmn := sub_mul_correspondence _ _ _ _ Hm Hn.
    have Hfmn := Hf _ _ Hmn.
    have Hmfn := sub_mul_correspondence _ _ _ _ Hm Hfn.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ Hmfn Hfmn)
      (HR HsuperR nR mR)).
  - intro HL. apply strictly_inhabits.
    intros HsuperR nR mR.
    have Hn := sub_nat_rel_canonical nR.
    have Hm := sub_nat_rel_canonical mR.
    have HsuperL := prop_to_sprop _ _
      (superadditive_correspondence fR fL Hf) HsuperR.
    have Hfn := Hf _ _ Hn.
    have Hmn := sub_mul_correspondence _ _ _ _ Hm Hn.
    have Hfmn := Hf _ _ Hmn.
    have Hmfn := sub_mul_correspondence _ _ _ _ Hm Hfn.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ Hmfn Hfmn)
      (HL HsuperL _ _)).
Qed.

Lemma superadditivity_leq_mul_statement_certificate :
  PropSPropRel
    OfficialSuperadditivityArithmetic.statement_superadditive_leq_mul
    superadditivity_leq_mul_target_statement.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL.
    set (fR := fun nR : nat =>
      sub_nat_to_rocq (fL (sub_nat_to_imported nR))).
    pose (Hf := superadditivity_pullback_related fL).
    exact (prop_to_sprop _ _
      (superadditivity_leq_mul_related fR fL Hf) (HR fR)).
  - intro HL. apply strictly_inhabits. intro fR.
    set (fL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fR (sub_nat_to_rocq nL))).
    pose (Hf := superadditivity_pushforward_related fR).
    exact (sprop_to_prop _ _
      (superadditivity_leq_mul_related fR fL Hf) (HL fL)).
Qed.

Lemma superadditivity_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR)
    (ImportedSuperadditivity.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn]. apply (ImportedSuperadditivity.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)).
    exact (prop_to_sprop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Definition superadditivity_unbounded_target_statement : SProp :=
  forall fL : Lean.Nat -> Lean.Nat,
    ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL ->
    ImportedSuperadditivity.Exists Lean.Nat
      (fun nL => sub_imported_lt superadditivity_target_zero (fL nL)) ->
    forall tL : Lean.Nat,
      ImportedSuperadditivity.Exists Lean.Nat
        (fun nL => sub_imported_le tL (fL nL)).

Lemma superadditivity_unbounded_related
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (Hf : SubNatFunRel fR fL) :
  PropSPropRel
    (OfficialSuperadditivityArithmetic.superadditive fR ->
      (exists nR : nat, is_true (ltn O (fR nR))) ->
      forall tR : nat,
        exists nR : nat, is_true (leq tR (fR nR)))
    (ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL ->
      ImportedSuperadditivity.Exists Lean.Nat
        (fun nL => sub_imported_lt superadditivity_target_zero (fL nL)) ->
      forall tL : Lean.Nat,
        ImportedSuperadditivity.Exists Lean.Nat
          (fun nL => sub_imported_le tL (fL nL))).
Proof.
  have Hpositive : PropSPropRel
    (exists nR : nat, is_true (ltn O (fR nR)))
    (ImportedSuperadditivity.Exists Lean.Nat
      (fun nL => sub_imported_lt superadditivity_target_zero (fL nL))).
  { apply superadditivity_exists_nat_correspondence.
    intros nR nL Hn. exact (sub_nat_lt_correspondence _ _ _ _
      (sub_nat_rel_canonical O) (Hf nR nL Hn)). }
  apply prop_sprop_rel_intro.
  - intros HR HsuperL HposL tL.
    set (tR := sub_nat_to_rocq tL).
    have Ht := sub_nat_rel_surjective tL.
    have HsuperR := sprop_to_prop _ _
      (superadditive_correspondence fR fL Hf) HsuperL.
    have HposR := sprop_to_prop _ _ Hpositive HposL.
    have Hexists : PropSPropRel
        (exists nR : nat, is_true (leq tR (fR nR)))
        (ImportedSuperadditivity.Exists Lean.Nat
          (fun nL => sub_imported_le tL (fL nL))).
    { apply superadditivity_exists_nat_correspondence.
      intros nR nL Hn.
      exact (sub_nat_le_correspondence _ _ _ _ Ht (Hf nR nL Hn)). }
    exact (prop_to_sprop _ _ Hexists (HR HsuperR HposR tR)).
  - intro HL. apply strictly_inhabits.
    intros HsuperR HposR tR.
    have Ht := sub_nat_rel_canonical tR.
    have HsuperL := prop_to_sprop _ _
      (superadditive_correspondence fR fL Hf) HsuperR.
    have HposL := prop_to_sprop _ _ Hpositive HposR.
    have Hexists : PropSPropRel
        (exists nR : nat, is_true (leq tR (fR nR)))
        (ImportedSuperadditivity.Exists Lean.Nat
          (fun nL => sub_imported_le (sub_nat_to_imported tR) (fL nL))).
    { apply superadditivity_exists_nat_correspondence.
      intros nR nL Hn.
      exact (sub_nat_le_correspondence _ _ _ _ Ht (Hf nR nL Hn)). }
    exact (sprop_to_prop _ _ Hexists
      (HL HsuperL HposL (sub_nat_to_imported tR))).
Qed.

Lemma superadditivity_unbounded_statement_certificate :
  PropSPropRel
    OfficialSuperadditivityArithmetic.statement_superadditive_unbounded
    superadditivity_unbounded_target_statement.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL.
    set (fR := fun nR : nat =>
      sub_nat_to_rocq (fL (sub_nat_to_imported nR))).
    pose (Hf := superadditivity_pullback_related fL).
    exact (prop_to_sprop _ _
      (superadditivity_unbounded_related fR fL Hf) (HR fR)).
  - intro HL. apply strictly_inhabits. intro fR.
    set (fL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fR (sub_nat_to_rocq nL))).
    pose (Hf := superadditivity_pushforward_related fR).
    exact (sprop_to_prop _ _
      (superadditivity_unbounded_related fR fL Hf) (HL fL)).
Qed.

Print Assumptions superadditivity_first_zero_statement_certificate.
Print Assumptions superadditivity_leq_mul_statement_certificate.
Print Assumptions superadditivity_unbounded_statement_certificate.
