From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import GeneratedMinmaxSource.
From FoundationImported Require Import ImportedMinmax.
From FoundationCertificates Require Import
  SubadditivityNatCorrespondence MinmaxCorrespondence MinmaxCertificate.

(** Exact guards: each encoded semantic target must typecheck by specializing
    the corresponding theorem constant from the actual imported artifact. *)

Check GeneratedMinmaxSource.statement_leq_bigmax_cond_seq.
Check GeneratedMinmaxSource.statement_leq_bigmax_sup.
Check GeneratedMinmaxSource.statement_bigmax_leq_seqP.
Check GeneratedMinmaxSource.statement_leq_big_max.
Check GeneratedMinmaxSource.statement_bigmax_ord_ltn_identity.
Check GeneratedMinmaxSource.statement_bigmax_ltn_ord.
Check GeneratedMinmaxSource.statement_bigmax_pred.
Check GeneratedMinmaxSource.statement_bigmax_witness.
Check GeneratedMinmaxSource.statement_bigmax_witness_diff.
Check GeneratedMinmaxSource.statement_bigmax_subset.

Definition exact_target_leq_bigmax_cond_seq_guard :
    mm_target_leq_bigmax_cond_seq_statement :=
  fun X F P xs x =>
    ImportedMinmax.Prosa_Util_Minmax_leq_bigmax_cond_seq
      (X : Type) (mm_decidable_eq X) (mm_nat_fun_to_imported F)
      (mm_pred_to_imported P) (mm_to_imported xs) x.

Definition exact_target_leq_bigmax_sup_guard :
    mm_target_leq_bigmax_sup_statement :=
  fun X P F xs n =>
    ImportedMinmax.Prosa_Util_Minmax_leq_bigmax_sup
      (X : Type) (mm_decidable_eq X) (mm_pred_to_imported P)
      (mm_nat_fun_to_imported F) (mm_to_imported xs)
      (sub_nat_to_imported n).

Definition exact_target_bigmax_leq_seqP_guard :
    mm_target_bigmax_leq_seqP_statement :=
  fun X F P xs m =>
    ImportedMinmax.Prosa_Util_Minmax_bigmax_leq_seqP
      (X : Type) (mm_decidable_eq X) (mm_nat_fun_to_imported F)
      (mm_pred_to_imported P) (mm_to_imported xs)
      (sub_nat_to_imported m).

Definition exact_target_leq_big_max_guard :
    mm_target_leq_big_max_statement :=
  fun X F1 F2 P xs =>
    ImportedMinmax.Prosa_Util_Minmax_leq_big_max
      (X : Type) (mm_decidable_eq X)
      (mm_nat_fun_to_imported F1) (mm_nat_fun_to_imported F2)
      (mm_pred_to_imported P) (mm_to_imported xs).

Definition exact_target_bigmax_ord_ltn_identity_guard :
    mm_target_bigmax_ord_ltn_identity_statement :=
  fun n => ImportedMinmax.Prosa_Util_Minmax_bigmax_ord_ltn_identity
    (sub_nat_to_imported n).

Definition exact_target_bigmax_ltn_ord_guard :
    mm_target_bigmax_ltn_ord_statement :=
  fun n P i0 => ImportedMinmax.Prosa_Util_Minmax_bigmax_ltn_ord
    (sub_nat_to_imported n) (mm_nat_pred_to_imported P)
    (mm_ord_to_fin n i0).

Definition exact_target_bigmax_pred_guard :
    mm_target_bigmax_pred_statement :=
  fun n P i0 => ImportedMinmax.Prosa_Util_Minmax_bigmax_pred
    (sub_nat_to_imported n) (mm_nat_pred_to_imported P)
    (mm_ord_to_fin n i0).

Definition exact_target_bigmax_witness_guard :
    mm_target_bigmax_witness_statement :=
  fun T xs P F => ImportedMinmax.Prosa_Util_Minmax_bigmax_witness
    (T : Type) (mm_decidable_eq T) (mm_to_imported xs)
    (mm_pred_to_imported P) (mm_nat_fun_to_imported F).

Definition exact_target_bigmax_witness_diff_guard :
    mm_target_bigmax_witness_diff_statement :=
  fun T xs P1 P2 F =>
    ImportedMinmax.Prosa_Util_Minmax_bigmax_witness_diff
      (T : Type) (mm_decidable_eq T) (mm_to_imported xs)
      (mm_pred_to_imported P1) (mm_pred_to_imported P2)
      (mm_nat_fun_to_imported F).

Definition exact_target_bigmax_subset_guard :
    mm_target_bigmax_subset_statement :=
  fun T xs P1 P2 F => ImportedMinmax.Prosa_Util_Minmax_bigmax_subset
    (T : Type) (mm_decidable_eq T) (mm_to_imported xs)
    (mm_pred_to_imported P1) (mm_pred_to_imported P2)
    (mm_nat_fun_to_imported F).

Print Assumptions exact_target_leq_bigmax_cond_seq_guard.
Print Assumptions exact_target_leq_bigmax_sup_guard.
Print Assumptions exact_target_bigmax_leq_seqP_guard.
Print Assumptions exact_target_leq_big_max_guard.
Print Assumptions exact_target_bigmax_ord_ltn_identity_guard.
Print Assumptions exact_target_bigmax_ltn_ord_guard.
Print Assumptions exact_target_bigmax_pred_guard.
Print Assumptions exact_target_bigmax_witness_guard.
Print Assumptions exact_target_bigmax_witness_diff_guard.
Print Assumptions exact_target_bigmax_subset_guard.
