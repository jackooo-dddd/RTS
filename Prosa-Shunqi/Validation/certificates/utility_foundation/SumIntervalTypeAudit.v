From mathcomp Require Import ssreflect ssrbool ssrnat seq bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSumInterval ImportedSubadditivity.
From FoundationCertificates Require Import
  SubadditivityNatCorrespondence SumIntervalCorrespondence
  SumIntervalCertificate.
Require Import GeneratedSumIntervalSource.

(** These declarations are type-provenance guards only.  The independent
    semantic certificates do not depend on them or on either theorem proof. *)

Definition target_sum_of_ones_exact_type_guard (t delta : nat) :
  target_sum_of_ones_statement t delta :=
  ImportedSumInterval.Prosa_Util_Sum_sum_of_ones
    (sub_nat_to_imported t) (sub_nat_to_imported delta).

Definition target_big_nat_eq0_exact_type_guard
    (m n : nat) (F : nat -> nat) :
  target_big_nat_eq0_statement m n F :=
  ImportedSumInterval.Prosa_Util_Sum_big_nat_eq0
    (sub_nat_to_imported m) (sub_nat_to_imported n)
    (sum_target_function F).

Definition target_sum_le_range_exact_type_guard
    (f : nat -> nat) (t delta : nat) :
  target_sum_le_range_statement f t delta :=
  ImportedSumInterval.Prosa_Util_Sum_sum_le_summation_range
    (sum_target_function f)
    (sub_nat_to_imported t) (sub_nat_to_imported delta).

Definition target_big_sum_eq_exact_type_guard :
  si_target_big_sum_eq_statement :=
  ImportedSumInterval.Prosa_Util_Sum_big_sum_eq_in_eq_sized_intervals.

Definition target_pigeonhole_exact_type_guard :
  si_target_pigeonhole_statement :=
  ImportedSumInterval.Prosa_Util_Sum_pigeonhole_on_interval.

Definition target_sum_ge_2_nat_exact_type_guard :
  si_target_sum_ge_2_nat_statement :=
  ImportedSumInterval.Prosa_Util_Sum_sum_ge_2_nat.

Check source_sum_of_ones_type_guard.
Check source_big_nat_eq0_type_guard.
Check source_sum_le_range_type_guard.
Check target_sum_of_ones_exact_type_guard.
Check target_big_nat_eq0_exact_type_guard.
Check target_sum_le_range_exact_type_guard.
Check source_big_sum_eq_type_guard.
Check source_pigeonhole_type_guard.
Check source_sum_ge_2_nat_type_guard.
Check target_big_sum_eq_exact_type_guard.
Check target_pigeonhole_exact_type_guard.
Check target_sum_ge_2_nat_exact_type_guard.
