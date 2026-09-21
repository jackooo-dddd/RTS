From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import ListRemCertificate
  ListBatch2Certificate.

(** Exact-type provenance guards.  They are intentionally separate from the
    independent semantic certificates. *)
Definition filter_in_pred0_target_type_guard :
    lb_target_filter_in_pred0_statement :=
  fun T => ImportedListLast.Prosa_Util_List_filter_in_pred0
    (T : Type) (lr_decidable_eq T).

Definition rem_all_target_type_guard :=
  ImportedListLast.Prosa_Util_List_rem_all.

Definition nin_rem_all_target_type_guard :
    lb_target_nin_rem_all_statement :=
  fun T => ImportedListLast.Prosa_Util_List_nin_rem_all
    (T : Type) (lr_decidable_eq T).

Definition in_rem_all_target_type_guard :
    lb_target_in_rem_all_statement :=
  fun T => ImportedListLast.Prosa_Util_List_in_rem_all
    (T : Type) (lr_decidable_eq T).

Definition rem_lt_id_target_type_guard : lb_target_rem_lt_id_statement :=
  ImportedListLast.Prosa_Util_List_rem_lt_id.
