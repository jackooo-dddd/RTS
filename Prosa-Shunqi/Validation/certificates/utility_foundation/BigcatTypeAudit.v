From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From FoundationImported Require Import ImportedBigcat.
From FoundationCertificates Require Import
  SubadditivityNatCorrespondence BigcatCorrespondence BigcatCertificate.
From prosa Require Import GeneratedBigcatSource.

(** These guards are deliberately separate from the semantic certificates.
    They force Rocq to check that each encoded target statement is exactly the
    type obtained by specializing the corresponding theorem from the actual
    imported Lean artifact through the approved representation maps. *)

Check GeneratedBigcatSource.statement_mem_bigcat_nat.
Check GeneratedBigcatSource.statement_mem_bigcat_nat_exists.
Check GeneratedBigcatSource.statement_mem_bigcat_ord.
Check GeneratedBigcatSource.statement_bigcat_nat_uniq.
Check GeneratedBigcatSource.statement_bigcat_nat_filter_eq_filter_bigcat_nat.
Check GeneratedBigcatSource.statement_size_big_nat.
Check GeneratedBigcatSource.statement_mem_bigcat.
Check GeneratedBigcatSource.statement_mem_bigcat_exists.
Check GeneratedBigcatSource.statement_bigcat_filter_eq_filter_bigcat.
Check GeneratedBigcatSource.statement_bigcat_uniq.
Check GeneratedBigcatSource.statement_seq_different_elements_nil.
Check GeneratedBigcatSource.statement_bigcat_seq_uniqK.
Check GeneratedBigcatSource.statement_bigcat_partitions.

Definition exact_target_mem_bigcat_nat_guard :
    bc_target_mem_bigcat_nat_statement :=
  fun T f x m n j =>
    ImportedBigcat.Prosa_Util_Bigcat_mem_bigcat_nat
      (T : Type) (bc_decidable_eq T) (bc_nat_family_to_imported f) x
      (sub_nat_to_imported m) (sub_nat_to_imported n)
      (sub_nat_to_imported j).

Definition exact_target_mem_bigcat_nat_exists_guard :
    bc_target_mem_bigcat_nat_exists_statement :=
  fun T f x m n =>
    ImportedBigcat.Prosa_Util_Bigcat_mem_bigcat_nat_exists
      (T : Type) (bc_decidable_eq T) (bc_nat_family_to_imported f) x
      (sub_nat_to_imported m) (sub_nat_to_imported n).

Definition exact_target_mem_bigcat_ord_guard :
    bc_target_mem_bigcat_ord_statement :=
  fun T x n j f =>
    ImportedBigcat.Prosa_Util_Bigcat_mem_bigcat_ord
      (T : Type) (bc_decidable_eq T) x (sub_nat_to_imported n)
      (bc_ord_to_fin n j) (bc_ord_family_to_imported n f).

Definition exact_target_bigcat_nat_uniq_guard :
    bc_target_bigcat_nat_uniq_statement :=
  fun T f =>
    ImportedBigcat.Prosa_Util_Bigcat_bigcat_nat_uniq
      (T : Type) (bc_decidable_eq T) (bc_nat_family_to_imported f).

Definition exact_target_bigcat_nat_filter_guard :
    bc_target_bigcat_nat_filter_statement :=
  fun X F P t1 t2 =>
    ImportedBigcat.Prosa_Util_Bigcat_bigcat_nat_filter_eq_filter_bigcat_nat
      X (bc_nat_family_to_imported F) (bc_pred_to_imported P)
      (sub_nat_to_imported t1) (sub_nat_to_imported t2).

Definition exact_target_size_big_nat_guard :
    bc_target_size_big_nat_statement :=
  fun X F t1 t2 =>
    ImportedBigcat.Prosa_Util_Bigcat_size_big_nat
      X (bc_nat_family_to_imported F)
      (sub_nat_to_imported t1) (sub_nat_to_imported t2).

Definition exact_target_mem_bigcat_guard :
    bc_target_mem_bigcat_statement :=
  fun X Y f x y s =>
    ImportedBigcat.Prosa_Util_Bigcat_mem_bigcat
      (X : Type) (Y : Type) (bc_decidable_eq X) (bc_decidable_eq Y)
      (bc_family_to_imported f) x y (bc_to_imported s).

Definition exact_target_mem_bigcat_exists_guard :
    bc_target_mem_bigcat_exists_statement :=
  fun X Y f P s y =>
    ImportedBigcat.Prosa_Util_Bigcat_mem_bigcat_exists
      (X : Type) (Y : Type) (bc_decidable_eq X) (bc_decidable_eq Y)
      (bc_family_to_imported f) (bc_pred_to_imported P)
      (bc_to_imported s) y.

Definition exact_target_bigcat_filter_guard :
    bc_target_bigcat_filter_eq_statement :=
  fun X Y f xss P =>
    ImportedBigcat.Prosa_Util_Bigcat_bigcat_filter_eq_filter_bigcat
      (X : Type) (Y : Type) (bc_decidable_eq X) (bc_decidable_eq Y)
      (bc_family_to_imported f) (bc_to_imported xss)
      (bc_pred_to_imported P).

Definition exact_target_bigcat_uniq_guard :
    bc_target_bigcat_uniq_statement :=
  fun X Y f xs P =>
    ImportedBigcat.Prosa_Util_Bigcat_bigcat_uniq
      (X : Type) (Y : Type) (bc_decidable_eq X) (bc_decidable_eq Y)
      (bc_family_to_imported f) (bc_to_imported xs)
      (bc_pred_to_imported P).

Definition exact_target_seq_different_elements_nil_guard :
    bc_target_seq_different_elements_nil_statement :=
  fun X Y f g =>
    ImportedBigcat.Prosa_Util_Bigcat_seq_different_elements_nil
      (X : Type) (Y : Type) (bc_decidable_eq X) (bc_decidable_eq Y)
      (bc_family_to_imported f) g.

Definition exact_target_bigcat_seq_uniqK_guard :
    bc_target_bigcat_seq_uniqK_statement :=
  fun X Y f g Hcancel y xs =>
    ImportedBigcat.Prosa_Util_Bigcat_bigcat_seq_uniqK
      (X : Type) (Y : Type) (bc_decidable_eq X) (bc_decidable_eq Y)
      (bc_family_to_imported f) g Hcancel y (bc_to_imported xs).

Definition exact_target_bigcat_partitions_guard :
    bc_target_bigcat_partitions_statement :=
  fun X Y xs ys P xToY =>
    ImportedBigcat.Prosa_Util_Bigcat_bigcat_partitions
      (X : Type) (Y : Type) (bc_decidable_eq X) (bc_decidable_eq Y)
      (bc_to_imported xs) (bc_to_imported ys)
      (bc_pred_to_imported P) xToY.

Print Assumptions exact_target_mem_bigcat_nat_guard.
Print Assumptions exact_target_mem_bigcat_nat_exists_guard.
Print Assumptions exact_target_mem_bigcat_ord_guard.
Print Assumptions exact_target_bigcat_nat_uniq_guard.
Print Assumptions exact_target_bigcat_nat_filter_guard.
Print Assumptions exact_target_size_big_nat_guard.
Print Assumptions exact_target_mem_bigcat_guard.
Print Assumptions exact_target_mem_bigcat_exists_guard.
Print Assumptions exact_target_bigcat_filter_guard.
Print Assumptions exact_target_bigcat_uniq_guard.
Print Assumptions exact_target_seq_different_elements_nil_guard.
Print Assumptions exact_target_bigcat_seq_uniqK_guard.
Print Assumptions exact_target_bigcat_partitions_guard.
