From mathcomp Require Import ssreflect ssrbool ssrnat seq bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSumInterval ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Computational correspondence for the exact normalized finite-sum
    interface exported from the fresh compiled [Prosa.Util.Sum] artifact. *)

Definition sum_target_one : Lean.Nat :=
  ImportedSumInterval.OfNat_ofNat_inst1 Lean.Nat (Lean.Nat_succ Lean.Nat_zero)
    (ImportedSumInterval.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition sum_target_function (F : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun n => sub_nat_to_imported (F (sub_nat_to_rocq n)).

Lemma sum_target_add_canonical (a b : nat) :
  Lean.eq
    (Lean.Nat_add
      (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a + b)).
Proof. exact (sub_add_canonical a b). Qed.

Lemma sum_target_add_canonical_prop (a b : nat) :
  Logic.eq
    (Lean.Nat_add
      (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a + b)).
Proof. exact (imported_eq_to_coq_eq _ _ (sum_target_add_canonical a b)). Qed.

Lemma sum_target_sub_succ_prop (a b : Lean.Nat) :
  Logic.eq
    (ImportedSumInterval.Nat_sub a (Lean.Nat_succ b))
    (ImportedSumInterval.Nat_pred (ImportedSumInterval.Nat_sub a b)).
Proof. reflexivity. Qed.

Lemma sum_target_zero_sub_prop (b : nat) :
  Logic.eq
    (ImportedSumInterval.Nat_sub Lean.Nat_zero (sub_nat_to_imported b))
    Lean.Nat_zero.
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rw sum_target_sub_succ_prop IH. reflexivity.
Qed.

Lemma sum_target_succ_sub_succ_prop (a b : nat) :
  Logic.eq
    (ImportedSumInterval.Nat_sub
      (Lean.Nat_succ (sub_nat_to_imported a))
      (Lean.Nat_succ (sub_nat_to_imported b)))
    (ImportedSumInterval.Nat_sub
      (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rw !sum_target_sub_succ_prop.
    exact (f_equal ImportedSumInterval.Nat_pred IH).
Qed.

Lemma sum_target_sub_canonical_prop (a b : nat) :
  Logic.eq
    (ImportedSumInterval.Nat_sub
      (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  induction b as [|b IH] in a |- *.
  - destruct a; reflexivity.
  - destruct a as [|a].
    + exact (sum_target_zero_sub_prop b.+1).
    + rw sum_target_succ_sub_succ_prop. exact (IH a).
Qed.

Lemma sum_target_range_succ_prop (start len step : Lean.Nat) :
  Logic.eq
    (ImportedSumInterval.List_range' start (Lean.Nat_succ len) step)
    (ImportedSumInterval.List_cons_inst1 Lean.Nat start
      (ImportedSumInterval.List_range'
        (Lean.Nat_add start step) len step)).
Proof. reflexivity. Qed.

Lemma sum_target_map_cons_prop {A B : Type} (f : A -> B) (x : A)
    (xs : ImportedSumInterval.List_inst1 A) :
  Logic.eq
    (ImportedSumInterval.List_map_inst3 A B f
      (ImportedSumInterval.List_cons_inst1 A x xs))
    (ImportedSumInterval.List_cons_inst1 B (f x)
      (ImportedSumInterval.List_map_inst3 A B f xs)).
Proof. reflexivity. Qed.

Lemma sum_target_foldr_cons_prop {A B : Type} (f : A -> B -> B)
    (z : B) (x : A) (xs : ImportedSumInterval.List_inst1 A) :
  Logic.eq
    (ImportedSumInterval.List_foldr_inst3 A B f z
      (ImportedSumInterval.List_cons_inst1 A x xs))
    (f x (ImportedSumInterval.List_foldr_inst3 A B f z xs)).
Proof. reflexivity. Qed.

Fixpoint sum_seq_to_target (xs : seq nat) :
    ImportedSumInterval.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedSumInterval.List_nil_inst1 Lean.Nat
  | x :: xs' => ImportedSumInterval.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (sum_seq_to_target xs')
  end.

Lemma sum_target_range_iota_prop (start len : nat) :
  Logic.eq
    (ImportedSumInterval.List_range'
      (sub_nat_to_imported start) (sub_nat_to_imported len) sum_target_one)
    (sum_seq_to_target (iota start len)).
Proof.
  elim: len start => [|len IH] start.
  - reflexivity.
  - cbn [sub_nat_to_imported iota sum_seq_to_target].
    rw sum_target_range_succ_prop.
    have Hstart : Logic.eq
        (Lean.Nat_add
          (sub_nat_to_imported start) sum_target_one)
        (sub_nat_to_imported start.+1) by reflexivity.
    rw Hstart (IH start.+1). reflexivity.
Qed.

Lemma sum_target_map_converted_prop (F : nat -> nat) (xs : seq nat) :
  Logic.eq
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat
      (sum_target_function F) (sum_seq_to_target xs))
    (sum_seq_to_target (map F xs)).
Proof.
  elim: xs => [|x xs IH].
  - reflexivity.
  - cbn [sum_seq_to_target]. rw sum_target_map_cons_prop.
    unfold sum_target_function.
    rw sub_nat_rocq_roundtrip IH. reflexivity.
Qed.

Definition sum_target_list_sum
    (xs : ImportedSumInterval.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedSumInterval.List_foldr_inst3 Lean.Nat Lean.Nat
    Lean.Nat_add Lean.Nat_zero xs.

Lemma sum_target_list_sum_converted_prop (xs : seq nat) :
  Logic.eq (sum_target_list_sum (sum_seq_to_target xs))
    (sub_nat_to_imported (foldr addn O xs)).
Proof.
  elim: xs => [|x xs IH].
  - reflexivity.
  - cbn [sum_seq_to_target foldr].
    unfold sum_target_list_sum.
    unfold sum_target_list_sum in IH.
    rw sum_target_foldr_cons_prop IH.
    exact (sum_target_add_canonical_prop x (foldr addn O xs)).
Qed.

Definition sum_target_interval_value
    (m n : nat) (F : nat -> nat) : Lean.Nat :=
  sum_target_list_sum
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat
      (sum_target_function F)
      (ImportedSumInterval.List_range'
        (sub_nat_to_imported m)
        (ImportedSumInterval.Nat_sub
          (sub_nat_to_imported n) (sub_nat_to_imported m))
        sum_target_one)).

Lemma mathcomp_big_seq_as_fold (xs : seq nat) (F : nat -> nat) :
  Logic.eq (\sum_(i <- xs) F i) (foldr addn O (map F xs)).
Proof.
  elim: xs => [|x xs IH].
  - rw big_nil. reflexivity.
  - rw big_cons. cbn [map foldr]. now rw IH.
Qed.

Lemma sum_target_interval_value_prop (m n : nat) (F : nat -> nat) :
  Logic.eq (sum_target_interval_value m n F)
    (sub_nat_to_imported (\sum_(m <= i < n) F i)).
Proof.
  unfold sum_target_interval_value.
  rw sum_target_sub_canonical_prop.
  rw sum_target_range_iota_prop.
  rw sum_target_map_converted_prop.
  rw sum_target_list_sum_converted_prop.
  rw /index_iota mathcomp_big_seq_as_fold.
  reflexivity.
Qed.

Theorem finite_nat_sum_value_correspondence (m n : nat) (F : nat -> nat) :
  Lean.eq (sum_target_interval_value m n F)
    (sub_nat_to_imported (\sum_(m <= i < n) F i)).
Proof.
  exact (coq_eq_to_imported_eq _ _
    (sum_target_interval_value_prop m n F)).
Qed.
