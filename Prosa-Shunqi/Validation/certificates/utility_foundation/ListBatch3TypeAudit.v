From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import ListRemCertificate
  ListBatch3Certificate.

(** Exact-type provenance guards.  These declarations bind the structural
    target propositions used by the independent semantic certificates to the
    theorem types exported from the current compiled Lean snapshot. *)
Definition subseq_leq_size_target_type_guard :
    l3_target_subseq_leq_size_statement :=
  fun T => ImportedListLast.Prosa_Util_List_subseq_leq_size
    (T : Type) (lr_decidable_eq T).

Definition in_zip_target_type_guard : l3_target_in_zip_statement :=
  fun T U => ImportedListLast.Prosa_Util_List_in_zip
    (T : Type) (U : Type) (lr_decidable_eq T) (lr_decidable_eq U).

Definition eq_ind_in_seq_target_type_guard :
    l3_target_eq_ind_in_seq_statement :=
  fun T => ImportedListLast.Prosa_Util_List_eq_ind_in_seq
    (T : Type) (lr_decidable_eq T).

Definition default_or_in_target_type_guard :
    l3_target_default_or_in_statement :=
  fun T => ImportedListLast.Prosa_Util_List_default_or_in
    (T : Type) (lr_decidable_eq T).

Definition exists_two_target_type_guard : l3_target_exists_two_statement :=
  fun T => ImportedListLast.Prosa_Util_List_exists_two
    (T : Type) (lr_decidable_eq T).

Definition has_all_nilp_target_type_guard :
    l3_target_has_all_nilp_statement :=
  fun T => ImportedListLast.Prosa_Util_List_has_all_nilp
    (T : Type) (lr_decidable_eq T).

Definition sorted_split_target_type_guard :
    l3_target_sorted_split_statement :=
  fun T => ImportedListLast.Prosa_Util_List_sorted_split
    (T : Type) (lr_decidable_eq T).

Definition sorted_cat_target_type_guard : l3_target_sorted_cat_statement :=
  fun T => ImportedListLast.Prosa_Util_List_sorted_cat
    (T : Type) (lr_decidable_eq T).

Definition nonnil_last_target_type_guard : l3_target_nonnil_last_statement :=
  fun T => ImportedListLast.Prosa_Util_List_nonnil_last
    (T : Type) (lr_decidable_eq T).
