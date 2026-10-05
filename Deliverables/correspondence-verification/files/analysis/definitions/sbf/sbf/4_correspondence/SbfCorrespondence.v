From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSbf.
From FoundationCertificates Require Import SubadditivityNatCorrespondence.
Require Import OfficialSbf.

(** The source single-field Class elaborates to a function type, while the
    actual imported Lean class is a primitive one-field record.  The
    representation relation is therefore observational and two-sided. *)
Definition SbfSource := OfficialSbf.OfficialSbf.SupplyBoundFunction.
Definition SbfTarget :=
  ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction.

Definition sbf_target_value (s : SbfTarget) (t : Lean.Nat) : Lean.Nat :=
  ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
    s t.

Definition SbfRel (sR : SbfSource) (sL : SbfTarget) : SProp :=
  forall tR tL, SubNatRel tR tL -> SubNatRel (sR tR) (sbf_target_value sL tL).

Definition sbf_export (sR : SbfSource) : SbfTarget :=
  ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
    (fun tL => sub_nat_to_imported (sR (sub_nat_to_rocq tL))).

Definition sbf_import (sL : SbfTarget) : SbfSource :=
  fun tR => sub_nat_to_rocq (sbf_target_value sL (sub_nat_to_imported tR)).

Lemma sbf_export_preserves_field (sR : SbfSource) :
  SbfRel sR (sbf_export sR).
Proof.
  intros tR tL Ht. destruct Ht.
  unfold SbfRel, sbf_target_value, sbf_export, SubNatRel in *.
  simpl. rewrite (sub_nat_rocq_roundtrip tR).
  exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported (sR tR))).
Qed.

Lemma sbf_import_preserves_field (sL : SbfTarget) :
  SbfRel (sbf_import sL) sL.
Proof.
  intros tR tL Ht. destruct Ht.
  unfold SubNatRel, sbf_import.
  exact (sub_nat_imported_roundtrip
    (sbf_target_value sL (sub_nat_to_imported tR))).
Qed.

Lemma sbf_source_roundtrip (sR : SbfSource) (tR : nat) :
  Logic.eq (sbf_import (sbf_export sR) tR) (sR tR).
Proof.
  unfold sbf_import, sbf_export, sbf_target_value.
  simpl. rewrite (sub_nat_rocq_roundtrip tR).
  exact (sub_nat_rocq_roundtrip (sR tR)).
Qed.

Lemma sbf_target_roundtrip (sL : SbfTarget) (tL : Lean.Nat) :
  Lean.eq (sbf_target_value (sbf_export (sbf_import sL)) tL)
    (sbf_target_value sL tL).
Proof.
  unfold sbf_export, sbf_import, sbf_target_value.
  simpl.
  exact (sub_imported_eq_trans _ _ _
    (sub_nat_imported_roundtrip
      (ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
        sL (sub_nat_to_imported (sub_nat_to_rocq tL))))
    (sub_imported_eq_congr
      (ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL)
      _ _ (sub_nat_imported_roundtrip tL))).
Qed.

Print Assumptions sbf_export_preserves_field.
Print Assumptions sbf_import_preserves_field.
Print Assumptions sbf_source_roundtrip.
Print Assumptions sbf_target_roundtrip.
