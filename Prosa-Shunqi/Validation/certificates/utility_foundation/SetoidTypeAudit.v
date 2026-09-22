From Stdlib Require Import Basics Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From FoundationImported Require Import ImportedSetoid.
From FoundationCertificates Require Import SetoidCorrespondence SetoidCertificate.
Require Import prosa.util.setoid.

(** The official source proof constants occur only in exact-type guards. *)
Definition exact_source_leb_eq_guard : st_source_leb_eq_statement :=
  prosa.util.setoid.leb_eq.

Definition exact_source_leqRW_guard : st_source_leqRW_statement :=
  @prosa.util.setoid.leqRW.

(** The actual imported target constants occur only in exact-type guards. *)
Definition exact_target_leb_eq_guard : st_target_leb_eq_statement :=
  ImportedSetoid.Prosa_Util_Setoid_leb_eq.

Definition exact_target_leqRW_guard : st_target_leqRW_statement :=
  ImportedSetoid.Prosa_Util_Setoid_leqRW.

(** Constructor signatures bind the public source and target inductives. *)
Definition exact_source_leb_constructor_guard :
    forall a b : bool,
      (is_true a -> is_true b) -> prosa.util.setoid.leb a b :=
  fun a b H => prosa.util.setoid.Leb a b (proj2 (st_implb_truth a b) H).

Definition exact_target_leb_constructor_guard :
    forall a b : ImportedSetoid.Bool,
      (Lean.eq a ImportedSetoid.Bool_true ->
       Lean.eq b ImportedSetoid.Bool_true) -> st_target_leb a b :=
  ImportedSetoid.Prosa_Util_Setoid_leb_intro.

Print Assumptions exact_source_leb_eq_guard.
Print Assumptions exact_target_leb_eq_guard.
Print Assumptions exact_source_leqRW_guard.
Print Assumptions exact_target_leqRW_guard.
Print Assumptions exact_source_leb_constructor_guard.
Print Assumptions exact_target_leb_constructor_guard.
