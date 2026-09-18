From Stdlib Require Import Arith.PeanoNat.
From LeanImport Require Import Lean.
Require Import ImportedEasy93.

Fixpoint rocq_nat_to_imported (n : nat) : Nat :=
  match n with
  | O => Nat_zero
  | S n' => Nat_succ (rocq_nat_to_imported n')
  end.

Fixpoint imported_nat_to_rocq (n : Nat) : nat :=
  match n with
  | Nat_zero => O
  | Nat_succ n' => S (imported_nat_to_rocq n')
  end.

Definition ImportedNatRel (nR : nat) (nL : Nat) : SProp :=
  eq (rocq_nat_to_imported nR) nL.

Lemma rocq_nat_roundtrip (n : nat) :
  Logic.eq (imported_nat_to_rocq (rocq_nat_to_imported n)) n.
Proof.
  induction n; cbn.
  - reflexivity.
  - f_equal. exact IHn.
Qed.

Definition imported_nat_succ_congr (a b : Nat) :
    eq a b -> eq (Nat_succ a) (Nat_succ b) :=
  fun H =>
    match H in eq _ z return eq (Nat_succ a) (Nat_succ z) with
    | eq_refl _ => eq_refl (Nat_succ a)
    end.

Lemma imported_nat_roundtrip (n : Nat) :
  eq (rocq_nat_to_imported (imported_nat_to_rocq n)) n.
Proof.
  induction n; cbn.
  - exact (eq_refl Nat_zero).
  - exact (imported_nat_succ_congr _ _ IHn).
Qed.

Lemma imported_nat_rel_intro (n : nat) :
  ImportedNatRel n (rocq_nat_to_imported n).
Proof. exact (eq_refl (rocq_nat_to_imported n)). Qed.

Lemma imported_nat_rel_functional nR nL :
  ImportedNatRel nR nL ->
  Logic.eq (imported_nat_to_rocq nL) nR.
Proof.
  intro H. destruct H. exact (rocq_nat_roundtrip nR).
Qed.

Print Assumptions rocq_nat_roundtrip.
Print Assumptions imported_nat_roundtrip.
