From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From FoundationImported Require Import ImportedPoet.
From FoundationCertificates Require Import PoetCorrespondence PoetCertificate.
From prosa Require Import GeneratedPoetSource.

(** The generated source signature is taken from the pinned inventory's
    elaborated [Check @declaration] evidence.  Full [util/list.v] compilation
    under Rocq 9.3 overflows in an unrelated early legacy proof, so the source
    proof constant is deliberately absent from this validation environment. *)
Check GeneratedPoetSource.statement_forall_exists_implied_by_forall_in_zip.

Definition poet_exact_target_type_guard : po_encoded_target_statement :=
  fun X Y PBool PProp xs =>
    ImportedPoet.Prosa_Util_Poet_forall_exists_implied_by_forall_in_zip
      (X : Type) (Y : Type) (po_decidable_eq X) (po_decidable_eq Y)
      (po_pair_pred_to_imported PBool) (po_prop_to_sprop PProp)
      (po_list_to_imported xs).

Print Assumptions poet_exact_target_type_guard.
