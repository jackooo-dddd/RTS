From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop ssrfun.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBigop.
From FoundationCertificates Require Import BigopCorrespondence BigopCertificate.
From prosa Require Import GeneratedBigopSource.
Require Import prosa.util.bigop.

(** Official source proof constant is used only as an exact elaborated-type
    guard, never by the semantic correspondence certificate. *)
Definition exact_source_big_pred1_seq_guard :
    GeneratedBigopSource.statement_big_pred1_seq :=
  prosa.util.bigop.big_pred1_seq.

(** The actual imported theorem is specialized only through the approved
    eqType and Monoid.law representation maps. *)
Definition exact_target_big_pred1_seq_guard :
    bo_target_big_pred1_seq_statement :=
  fun R idx op T =>
    ImportedBigop.Prosa_Util_Bigop_big_pred1_seq
      R idx op
      (bo_assoc_from_monoid R idx op)
      (bo_left_id_from_monoid R idx op)
      (bo_right_id_from_monoid R idx op)
      T (bo_decidable_eq T).

Print Assumptions exact_source_big_pred1_seq_guard.
Print Assumptions exact_target_big_pred1_seq_guard.
