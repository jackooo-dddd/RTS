From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import ListRemCertificate
  ListBatch4Certificate.

(** Kernel type guards: each structural proposition used by the independent
    semantic proof is definitionally the exact type of the freshly imported
    compiled Lean theorem. *)
Definition filter_last_mem_target_type_guard :
    l4_target_filter_last_mem_statement :=
  fun T => ImportedListLast.Prosa_Util_List_filter_last_mem
    (T : Type) (lr_decidable_eq T).

Definition iotaD_impl_target_type_guard : l4_target_iotaD_impl_statement :=
  ImportedListLast.Prosa_Util_List_iotaD_impl.

Definition index_iota_lt_step_target_type_guard :
    l4_target_index_iota_lt_step_statement :=
  ImportedListLast.Prosa_Util_List_index_iota_lt_step.

Definition index_iota_cat_target_type_guard :
    l4_target_index_iota_cat_statement :=
  ImportedListLast.Prosa_Util_List_index_iota_cat.

Definition range_filter_2cons_target_type_guard :
    l4_target_range_filter_2cons_statement :=
  ImportedListLast.Prosa_Util_List_range_filter_2cons.

Definition index_iota_filter_eqx_target_type_guard :
    l4_target_index_iota_filter_eqx_statement :=
  ImportedListLast.Prosa_Util_List_index_iota_filter_eqx.

Definition index_iota_filter_singl_target_type_guard :
    l4_target_index_iota_filter_singl_statement :=
  ImportedListLast.Prosa_Util_List_index_iota_filter_singl.

Definition index_iota_filter_inxs_target_type_guard :
    l4_target_index_iota_filter_inxs_statement :=
  ImportedListLast.Prosa_Util_List_index_iota_filter_inxs.

Check ImportedListLast.Prosa_Util_List_range.
Check range_definition_certificate.
