From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedEpsilon ImportedSubadditivity.
From FoundationCertificates Require Import SubadditivityNatCorrespondence.
Require Import EpsilonSourceInterface.

Definition epsilon_source_value : nat :=
  EpsilonSourceInterface.epsilon_nat_value.

Definition epsilon_target_value : Lean.Nat :=
  ImportedEpsilon.Prosa_Validation_EpsilonInterface_epsilonNatValue.

(** The notation on each side elaborates to its native numeral one.  The
    target is the body exported from a validation interface that imports the
    actual compiled production module. *)
Theorem epsilon_notation_value_certificate :
  SubNatRel epsilon_source_value epsilon_target_value.
Proof. exact (@Lean.eq_refl _ _). Qed.

Print Assumptions epsilon_notation_value_certificate.
