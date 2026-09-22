From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSumSequence.
From FoundationCertificates Require Import SumSequenceCorrespondence.
From FoundationCertificates Require Import SumSequenceCertificate.

(** These guards are the only place where the imported target theorem
    constants are referenced.  The semantic certificates themselves are
    independent of both source and target proof constants. *)

Definition exact_target_sum_nat_eq0_nat :
    ss_target_sum_nat_eq0_nat_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_sum_nat_eq0_nat
    (T : Type) (ss_decidable_eq T).

Definition exact_target_sum_nat_gt0 :
    ss_target_sum_nat_gt0_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_sum_nat_gt0
    (T : Type) (ss_decidable_eq T).

Definition exact_target_sum_majorant_constant :
    ss_target_sum_majorant_constant_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_sum_majorant_constant
    (T : Type) (ss_decidable_eq T).

Definition exact_target_bigmax_leq_sum :
    ss_target_bigmax_leq_sum_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_bigmax_leq_sum
    (T : Type) (ss_decidable_eq T).

Definition exact_target_sum_le_subseq :
    ss_target_sum_le_subseq_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_sum_le_subseq
    (T : Type) (ss_decidable_eq T).

Definition exact_target_leq_sum_subseq :
    ss_target_leq_sum_subseq_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_leq_sum_subseq
    (T : Type) (ss_decidable_eq T).

Definition exact_target_leq_sum_seq :
    ss_target_leq_sum_seq_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_leq_sum_seq
    (T : Type) (ss_decidable_eq T).

Definition exact_target_eq_sum_seq :
    ss_target_eq_sum_seq_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_eq_sum_seq
    (T : Type) (ss_decidable_eq T).

Definition exact_target_leq_sum_seq_pred :
    ss_target_leq_sum_seq_pred_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_leq_sum_seq_pred
    (T : Type) (ss_decidable_eq T).

Definition exact_target_ltn_sum_leq_seq :
    ss_target_ltn_sum_leq_seq_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_ltn_sum_leq_seq
    (T : Type) (ss_decidable_eq T).

Definition exact_target_eq_sum_leq_seq :
    ss_target_eq_sum_leq_seq_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_eq_sum_leq_seq
    (T : Type) (ss_decidable_eq T).

Definition exact_target_leq_sum_sub_uniq :
    ss_target_leq_sum_sub_uniq_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_leq_sum_sub_uniq
    (T : Type) (ss_decidable_eq T).

Definition exact_target_sum_split_exhaustive_mutually_exclusive_preds :
    ss_target_sum_split_statement :=
  fun T =>
    ImportedSumSequence.Prosa_Util_Sum_sum_split_exhaustive_mutually_exclusive_preds
      (T : Type) (ss_decidable_eq T).

Definition exact_target_sum_over_partitions_le :
    ss_target_sum_over_partitions_le_statement :=
  fun X Y => ImportedSumSequence.Prosa_Util_Sum_sum_over_partitions_le
    (X : Type) (Y : Type) (ss_decidable_eq X) (ss_decidable_eq Y).

Definition exact_target_reorder_summation :
    ss_target_reorder_summation_statement :=
  fun X Y => ImportedSumSequence.Prosa_Util_Sum_reorder_summation
    (X : Type) (Y : Type) (ss_decidable_eq X) (ss_decidable_eq Y).

Definition exact_target_sum_over_partitions_eq :
    ss_target_sum_over_partitions_eq_statement :=
  fun X Y => ImportedSumSequence.Prosa_Util_Sum_sum_over_partitions_eq
    (X : Type) (Y : Type) (ss_decidable_eq X) (ss_decidable_eq Y).

Definition exact_target_sum_leq_mono :
    ss_target_sum_leq_mono_statement :=
  fun I => ImportedSumSequence.Prosa_Util_Sum_sum_leq_mono
    (I : Type) (ss_decidable_eq I).

Definition exact_target_sum_unit1 : ss_target_sum_unit1_statement :=
  ImportedSumSequence.Prosa_Util_Sum_sum_unit1.

Definition exact_target_sum_ge_2_seq : ss_target_sum_ge_2_seq_statement :=
  fun T => ImportedSumSequence.Prosa_Util_Sum_sum_ge_2_seq
    (T : Type) (ss_decidable_eq T).

Print Assumptions exact_target_sum_nat_eq0_nat.
Print Assumptions exact_target_sum_nat_gt0.
Print Assumptions exact_target_sum_majorant_constant.
Print Assumptions exact_target_bigmax_leq_sum.
Print Assumptions exact_target_sum_le_subseq.
Print Assumptions exact_target_leq_sum_subseq.
Print Assumptions exact_target_leq_sum_seq.
Print Assumptions exact_target_eq_sum_seq.
Print Assumptions exact_target_leq_sum_seq_pred.
Print Assumptions exact_target_ltn_sum_leq_seq.
Print Assumptions exact_target_eq_sum_leq_seq.
Print Assumptions exact_target_leq_sum_sub_uniq.
Print Assumptions exact_target_sum_split_exhaustive_mutually_exclusive_preds.
Print Assumptions exact_target_sum_over_partitions_le.
Print Assumptions exact_target_reorder_summation.
Print Assumptions exact_target_sum_over_partitions_eq.
Print Assumptions exact_target_sum_leq_mono.
Print Assumptions exact_target_sum_unit1.
Print Assumptions exact_target_sum_ge_2_seq.
