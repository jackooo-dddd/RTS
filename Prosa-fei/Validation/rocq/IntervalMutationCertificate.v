From mathcomp Require Import ssreflect ssrbool ssrnat bigop.
From LeanImport Require Import Lean.
Require Import ImportedIntervalMutation93.

Definition mutation_one : Nat := Nat_succ Nat_zero.
Definition mutation_one_function : Nat -> Nat := fun _ => mutation_one.

Definition source_empty_interval_value : nat :=
  \sum_(O <= i < O) (fun _ : nat => 1%N) i.

Lemma source_empty_interval_is_zero : Logic.eq source_empty_interval_value O.
Proof. by rewrite /source_empty_interval_value big_geq. Qed.

Lemma imported_original_empty_interval_is_zero :
  eq
    (Validation_IntervalMutationFixture_originalIcoSum
      Nat_zero Nat_zero mutation_one_function)
    Nat_zero.
Proof. exact (eq_refl _). Qed.

Lemma imported_positive_control_preserves_semantics
    (m n : Nat) (F : Nat -> Nat) :
  eq
    (Validation_IntervalMutationFixture_positiveControlSum
      m n F)
    (Validation_IntervalMutationFixture_originalIcoSum
      m n F).
Proof. exact (eq_refl _). Qed.

Lemma imported_mutated_closed_interval_is_one :
  eq
    (Validation_IntervalMutationFixture_mutatedIccSum
      Nat_zero Nat_zero mutation_one_function)
    mutation_one.
Proof. exact (eq_refl _). Qed.

Inductive MutationContradiction : SProp := .

Definition mutation_succ_ne_zero (n : Nat) :
    eq (Nat_succ n) Nat_zero -> MutationContradiction :=
  fun H => match H in eq _ z return
    match z with Nat_zero => MutationContradiction | Nat_succ _ => True end
  with eq_refl => True_intro end.

(** End-to-end rejection: the actual imported closed-interval artifact cannot
    equal the official source value for m = n = 0 and F 0 = 1. *)
Theorem closed_endpoint_mutation_detected :
  eq
    (Validation_IntervalMutationFixture_mutatedIccSum
      Nat_zero Nat_zero mutation_one_function)
    Nat_zero -> MutationContradiction.
Proof.
  intro Hbad.
  exact (mutation_succ_ne_zero Nat_zero Hbad).
Qed.

Goal Logic.True. idtac "MUTATION_AUDIT original_ico". exact Logic.I. Qed.
Print Assumptions imported_original_empty_interval_is_zero.
Goal Logic.True. idtac "MUTATION_AUDIT positive_control". exact Logic.I. Qed.
Print Assumptions imported_positive_control_preserves_semantics.
Goal Logic.True. idtac "MUTATION_AUDIT mutated_icc". exact Logic.I. Qed.
Print Assumptions imported_mutated_closed_interval_is_one.
Goal Logic.True. idtac "MUTATION_AUDIT mutation_detected". exact Logic.I. Qed.
Print Assumptions closed_endpoint_mutation_detected.
