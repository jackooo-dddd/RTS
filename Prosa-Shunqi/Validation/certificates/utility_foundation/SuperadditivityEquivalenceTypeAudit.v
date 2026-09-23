From FoundationImported Require Import ImportedSuperadditivity.
From FoundationCertificates Require Import SuperadditivityEquivalenceCertificate
  SuperadditivityArithmeticCertificate SuperadditivityMonotoneCertificate
  SuperadditivityHorizonCertificate.

(** Provenance guard only: the semantic certificate does not import this
    module or call the theorem proof constant. *)
Definition superadditivity_equivalence_imported_exact_type :
    superadditivity_equivalence_target_statement :=
  ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_standard_equivalence.

Definition superadditivity_first_zero_imported_exact_type :
    superadditivity_first_zero_target_statement :=
  ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_first_zero.

Definition superadditivity_leq_mul_imported_exact_type :
    superadditivity_leq_mul_target_statement :=
  ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_leq_mul.

Definition superadditivity_unbounded_imported_exact_type :
    superadditivity_unbounded_target_statement :=
  ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_unbounded.

Definition superadditivity_monotone_imported_exact_type :
    superadditivity_monotone_target_statement :=
  ImportedSuperadditivity.Prosa_Util_Superadditivity_superadditive_monotone.

Definition superadditivity_horizon_at_imported_exact_type :
    sa_horizon_at_target_statement :=
  ImportedSuperadditivity.Prosa_Util_Superadditivity_minimal_extension_superadditive_at_horizon.

Definition superadditivity_horizon_until_imported_exact_type :
    sa_horizon_until_target_statement :=
  ImportedSuperadditivity.Prosa_Util_Superadditivity_minimal_extension_superadditive_until.
