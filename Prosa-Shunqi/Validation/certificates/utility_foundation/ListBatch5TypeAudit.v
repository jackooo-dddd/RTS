From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import ListRemCertificate
  ListBatch5Certificate.

(** Exact target-type guards against the current imported compiled artifact. *)
Definition index_iota_filter_step_target_type_guard :
    l5_target_index_iota_filter_step_statement :=
  ImportedListLast.Prosa_Util_List_index_iota_filter_step.

Definition range_iota_filter_step_target_type_guard :
    l5_target_range_iota_filter_step_statement :=
  ImportedListLast.Prosa_Util_List_range_iota_filter_step.

Definition iota_filter_gt_target_type_guard :
    l5_target_iota_filter_gt_statement :=
  ImportedListLast.Prosa_Util_List_iota_filter_gt.

Definition sub_count_seq_target_type_guard :
    l5_target_sub_count_seq_statement :=
  fun T => ImportedListLast.Prosa_Util_List_sub_count_seq
    (T : Type) (lr_decidable_eq T).

Definition count_predUI_target_type_guard :
    l5_target_count_predUI_statement :=
  ImportedListLast.Prosa_Util_List_count_predUI'.

Definition prefix_of_target_type_guard :
    forall (T : eqType), ImportedListLast.List T ->
      ImportedListLast.List T -> SProp :=
  fun T => ImportedListLast.Prosa_Util_List_prefix_of
    (T : Type) (lr_decidable_eq T).

Definition strict_prefix_of_target_type_guard :
    forall (T : eqType), ImportedListLast.List T ->
      ImportedListLast.List T -> SProp :=
  fun T => ImportedListLast.Prosa_Util_List_strict_prefix_of
    (T : Type) (lr_decidable_eq T).

Check ImportedListLast.Prosa_Util_List_shift_points_pos.
Check ImportedListLast.Prosa_Util_List_shift_points_neg.
Check shift_points_pos_definition_certificate.
Check shift_points_neg_definition_certificate.
