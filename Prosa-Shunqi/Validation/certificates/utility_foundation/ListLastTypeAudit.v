From mathcomp Require Import ssreflect ssrbool eqtype.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import ListLastCertificate ListRemCertificate.

(** Provenance-only guards: each assignment type-checks only when the exact
    freshly imported compiled theorem type is convertible to the structural
    target proposition used by the independent semantic certificate. *)
Definition last0_cons_target_type_guard : ll_target_last0_cons_statement :=
  ImportedListLast.Prosa_Util_List_last0_cons.

Definition last0_cat_target_type_guard : ll_target_last0_cat_statement :=
  ImportedListLast.Prosa_Util_List_last0_cat.

Definition last0_nth_target_type_guard : ll_target_last0_nth_statement :=
  ImportedListLast.Prosa_Util_List_last0_nth.

Definition last0_ex_cat_target_type_guard : ll_target_last0_ex_cat_statement :=
  ImportedListLast.Prosa_Util_List_last0_ex_cat.

Definition last0_filter_target_type_guard : ll_target_last0_filter_statement :=
  ImportedListLast.Prosa_Util_List_last0_filter.

Definition max0_cons_target_type_guard : ll_target_max0_cons_statement :=
  ImportedListLast.Prosa_Util_List_max0_cons.

Definition max0_2cons_eq_target_type_guard :
    ll_target_max0_2cons_eq_statement :=
  ImportedListLast.Prosa_Util_List_max0_2cons_eq.

Definition max0_2cons_le_target_type_guard :
    ll_target_max0_2cons_le_statement :=
  ImportedListLast.Prosa_Util_List_max0_2cons_le.

Definition last_of_seq_le_max_of_seq_target_type_guard :
    ll_target_last_le_max_statement :=
  ImportedListLast.Prosa_Util_List_last_of_seq_le_max_of_seq.

Definition max0_of_uniform_set_target_type_guard :
    ll_target_max0_of_uniform_set_statement :=
  ImportedListLast.Prosa_Util_List_max0_of_uniform_set.

Definition in_max0_le_target_type_guard : ll_target_in_max0_le_statement :=
  ImportedListLast.Prosa_Util_List_in_max0_le.

Definition max0_in_seq_target_type_guard : ll_target_max0_in_seq_statement :=
  ImportedListLast.Prosa_Util_List_max0_in_seq.

Definition max0_rem0_target_type_guard : ll_target_max0_rem0_statement :=
  ImportedListLast.Prosa_Util_List_max0_rem0.

Definition max_of_dominating_seq_target_type_guard :
    ll_target_max_of_dominating_seq_statement :=
  ImportedListLast.Prosa_Util_List_max_of_dominating_seq.

Definition nth0_cons_target_type_guard : ll_target_nth0_cons_statement :=
  ImportedListLast.Prosa_Util_List_nth0_cons.

Definition rem_in_target_type_guard : lr_target_rem_in_statement :=
  fun T => ImportedListLast.Prosa_Util_List_rem_in (T : Type)
    (lr_decidable_eq T).

Definition in_neq_impl_rem_in_target_type_guard :
    lr_target_in_neq_impl_rem_in_statement :=
  fun T => ImportedListLast.Prosa_Util_List_in_neq_impl_rem_in (T : Type)
    (lr_decidable_eq T).

Definition filter_size_rem_target_type_guard :
    lr_target_filter_size_rem_statement :=
  fun T => ImportedListLast.Prosa_Util_List_filter_size_rem (T : Type)
    (lr_decidable_eq T).

Definition in_seq_equiv_undup_target_type_guard :
    lr_target_in_seq_equiv_undup_statement :=
  fun T => ImportedListLast.Prosa_Util_List_in_seq_equiv_undup (T : Type)
    (lr_decidable_eq T).

Definition seq1_some_target_type_guard : lr_target_seq1_some_statement :=
  fun T => ImportedListLast.Prosa_Util_List_seq1_some (T : Type)
    (lr_decidable_eq T).

Definition seq_elim_last_target_type_guard :
    lr_target_seq_elim_last_statement :=
  ImportedListLast.Prosa_Util_List_seq_elim_last.

Definition in_cat_target_type_guard : lr_target_in_cat_statement :=
  fun T => ImportedListLast.Prosa_Util_List_in_cat (T : Type)
    (lr_decidable_eq T).
