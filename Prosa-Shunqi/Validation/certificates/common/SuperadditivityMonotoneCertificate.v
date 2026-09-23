From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSuperadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence SuperadditivityBaseCorrespondence
  SuperadditivityEquivalenceCertificate.
From prosa Require Import util.rel.
Require Import OfficialSuperadditivityMonotone.

Definition superadditivity_target_le (a b : Lean.Nat) : SProp :=
  ImportedSuperadditivity.LE_le_inst1 Lean.Nat
    ImportedSuperadditivity.instLENat a b.

Definition superadditivity_target_decide_le (a b : Lean.Nat) :
    ImportedSuperadditivity.Bool :=
  ImportedSuperadditivity.Decidable_decide (superadditivity_target_le a b)
    (ImportedSuperadditivity.Nat_decLe a b).

Definition superadditivity_false_elim (Q : SProp)
    (H : ImportedSuperadditivity.False) : Q := match H return Q with end.

Inductive SuperadditivityTrue : SProp := superadditivity_true_intro.

Definition superadditivity_bool_false_ne_true
    (H : Lean.eq ImportedSuperadditivity.Bool_false
      ImportedSuperadditivity.Bool_true) : ImportedSuperadditivity.False :=
  match H in Lean.eq _ z return
    match z with
    | ImportedSuperadditivity.Bool_false => SuperadditivityTrue
    | ImportedSuperadditivity.Bool_true => ImportedSuperadditivity.False
    end
  with Lean.eq_refl => superadditivity_true_intro end.

Definition superadditivity_decide_forward (P : SProp)
    (d : ImportedSuperadditivity.Decidable P) :
    P -> Lean.eq (ImportedSuperadditivity.Decidable_decide P d)
      ImportedSuperadditivity.Bool_true :=
  match d as d0 return
      P -> Lean.eq (ImportedSuperadditivity.Decidable_decide P d0)
        ImportedSuperadditivity.Bool_true
  with
  | ImportedSuperadditivity.Decidable_isTrue H =>
      fun _ => @Lean.eq_refl ImportedSuperadditivity.Bool
        ImportedSuperadditivity.Bool_true
  | ImportedSuperadditivity.Decidable_isFalse H =>
      fun p => superadditivity_false_elim _ (H p)
  end.

Definition superadditivity_decide_backward (P : SProp)
    (d : ImportedSuperadditivity.Decidable P) :
    Lean.eq (ImportedSuperadditivity.Decidable_decide P d)
      ImportedSuperadditivity.Bool_true -> P :=
  match d as d0 return
      Lean.eq (ImportedSuperadditivity.Decidable_decide P d0)
        ImportedSuperadditivity.Bool_true -> P
  with
  | ImportedSuperadditivity.Decidable_isTrue H => fun _ => H
  | ImportedSuperadditivity.Decidable_isFalse H =>
      fun Heq => superadditivity_false_elim _
        (superadditivity_bool_false_ne_true Heq)
  end.

Lemma superadditivity_decide_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR))
    (Lean.eq (superadditivity_target_decide_le aL bL)
      ImportedSuperadditivity.Bool_true).
Proof.
  intros Ha Hb.
  have Hle : PropSPropRel (is_true (leq aR bR))
      (superadditivity_target_le aL bL) :=
    sub_nat_le_correspondence aR aL bR bL Ha Hb.
  apply prop_sprop_rel_intro.
  - intro HR. apply superadditivity_decide_forward.
    exact (prop_to_sprop _ _ Hle HR).
  - intro HL. apply strictly_inhabits.
    exact (sprop_to_prop _ _ Hle
      (superadditivity_decide_backward _ _ HL)).
Qed.

Definition superadditivity_target_monotone
    (f : Lean.Nat -> Lean.Nat) : SProp :=
  ImportedSuperadditivity.Prosa_Util_Rel_monotone_inst1 Lean.Nat
    superadditivity_target_decide_le f.

Lemma superadditivity_monotone_related
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  PropSPropRel (prosa.util.rel.monotone leq fR)
    (superadditivity_target_monotone fL).
Proof.
  intro Hf. apply prop_sprop_rel_intro.
  - intros HR xL yL HxyL.
    set (xR := sub_nat_to_rocq xL).
    set (yR := sub_nat_to_rocq yL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
    have HxyR := sprop_to_prop _ _
      (superadditivity_decide_le_correspondence _ _ _ _ Hx Hy) HxyL.
    have Hfx := Hf _ _ Hx.
    have Hfy := Hf _ _ Hy.
    exact (prop_to_sprop _ _
      (superadditivity_decide_le_correspondence _ _ _ _ Hfx Hfy)
      (HR xR yR HxyR)).
  - intro HL. apply strictly_inhabits. intros xR yR HxyR.
    have Hx := sub_nat_rel_canonical xR.
    have Hy := sub_nat_rel_canonical yR.
    have HxyL := prop_to_sprop _ _
      (superadditivity_decide_le_correspondence _ _ _ _ Hx Hy) HxyR.
    have Hfx := Hf _ _ Hx.
    have Hfy := Hf _ _ Hy.
    exact (sprop_to_prop _ _
      (superadditivity_decide_le_correspondence _ _ _ _ Hfx Hfy)
      (HL _ _ HxyL)).
Qed.

Definition superadditivity_monotone_target_statement : SProp :=
  forall fL : Lean.Nat -> Lean.Nat,
    ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive fL ->
    superadditivity_target_monotone fL.

Lemma superadditivity_monotone_statement_certificate :
  PropSPropRel
    OfficialSuperadditivityMonotone.statement_superadditive_monotone
    superadditivity_monotone_target_statement.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL.
    set (fR := fun nR : nat =>
      sub_nat_to_rocq (fL (sub_nat_to_imported nR))).
    pose (Hf := superadditivity_pullback_related fL).
    intro HsuperL.
    have HsuperR := sprop_to_prop _ _
      (superadditive_correspondence fR fL Hf) HsuperL.
    exact (prop_to_sprop _ _
      (superadditivity_monotone_related fR fL Hf) (HR fR HsuperR)).
  - intro HL. apply strictly_inhabits. intro fR.
    set (fL := fun nL : Lean.Nat =>
      sub_nat_to_imported (fR (sub_nat_to_rocq nL))).
    pose (Hf := superadditivity_pushforward_related fR).
    intro HsuperR.
    have HsuperL := prop_to_sprop _ _
      (superadditive_correspondence fR fL Hf) HsuperR.
    exact (sprop_to_prop _ _
      (superadditivity_monotone_related fR fL Hf) (HL fL HsuperL)).
Qed.

Print Assumptions superadditivity_monotone_statement_certificate.
