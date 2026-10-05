From mathcomp Require Import ssreflect ssrbool ssrnat.
Require Import GeneratedSuperadditivitySourceBase OfficialSuperadditivityAll
  OfficialSuperadditivityEquiv OfficialSuperadditivityArithmetic
  OfficialSuperadditivityMonotone OfficialSuperadditivityExtension
  OfficialSuperadditivityHorizon.

(** Kernel conversion guards bind each proof-facing extracted source slice to
    the combined twelve-declaration slice used for publication. *)
Definition bind_superadditive_at : Logic.eq
  GeneratedSuperadditivitySourceBase.superadditive_at
  OfficialSuperadditivityAll.superadditive_at := Logic.eq_refl.
Definition bind_superadditive_until : Logic.eq
  GeneratedSuperadditivitySourceBase.superadditive_until
  OfficialSuperadditivityAll.superadditive_until := Logic.eq_refl.
Definition bind_superadditive : Logic.eq
  GeneratedSuperadditivitySourceBase.superadditive
  OfficialSuperadditivityAll.superadditive := Logic.eq_refl.
Definition bind_superadditive_standard : Logic.eq
  GeneratedSuperadditivitySourceBase.superadditive_standard
  OfficialSuperadditivityAll.superadditive_standard := Logic.eq_refl.
Definition bind_standard_equivalence : Logic.eq
  OfficialSuperadditivityEquiv.statement_superadditive_standard_equivalence
  OfficialSuperadditivityAll.statement_superadditive_standard_equivalence := Logic.eq_refl.
Definition bind_first_zero : Logic.eq
  OfficialSuperadditivityArithmetic.statement_superadditive_first_zero
  OfficialSuperadditivityAll.statement_superadditive_first_zero := Logic.eq_refl.
Definition bind_monotone : Logic.eq
  OfficialSuperadditivityMonotone.statement_superadditive_monotone
  OfficialSuperadditivityAll.statement_superadditive_monotone := Logic.eq_refl.
Definition bind_leq_mul : Logic.eq
  OfficialSuperadditivityArithmetic.statement_superadditive_leq_mul
  OfficialSuperadditivityAll.statement_superadditive_leq_mul := Logic.eq_refl.
Definition bind_unbounded : Logic.eq
  OfficialSuperadditivityArithmetic.statement_superadditive_unbounded
  OfficialSuperadditivityAll.statement_superadditive_unbounded := Logic.eq_refl.
Definition bind_minimal_extension : Logic.eq
  OfficialSuperadditivityExtension.minimal_superadditive_extension
  OfficialSuperadditivityAll.minimal_superadditive_extension := Logic.eq_refl.
Definition bind_horizon_at : Logic.eq
  OfficialSuperadditivityHorizon.statement_minimal_extension_superadditive_at_horizon
  OfficialSuperadditivityAll.statement_minimal_extension_superadditive_at_horizon := Logic.eq_refl.
Definition bind_horizon_until : Logic.eq
  OfficialSuperadditivityHorizon.statement_minimal_extension_superadditive_until
  OfficialSuperadditivityAll.statement_minimal_extension_superadditive_until := Logic.eq_refl.
