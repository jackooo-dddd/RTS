From mathcomp Require Import ssreflect ssrbool ssrnat bigop.
From LeanImport Require Import Lean.
Require Import ImportedBigNatEq093 PropSPropFoundation HardSumCertificate
  FiniteNatSumBridge.

(** Intentional semantic mutation: the imported sum is compared with one
    instead of zero.  Reusing the validated certificate must be rejected. *)
Definition imported_big_nat_eq1_mutation
    (m n : nat) (F : nat -> nat) : SProp :=
  Iff
    (eq (imported_interval_sum m n F) (Nat_succ Nat_zero))
    (forall i : Nat,
      And (Nat_le (sum_nat_to_imported m) i)
          (Nat_lt i (sum_nat_to_imported n)) ->
      eq (canonical_imported_function F i) Nat_zero).

Fail Definition big_nat_eq0_certificate_rejects_eq1_mutation
    (m n : nat) (F : nat -> nat) :
  PropSPropRel
    (source_big_nat_eq0_statement m n F)
    (imported_big_nat_eq1_mutation m n F) :=
  big_nat_eq0_closed_certificate m n F.

Definition big_nat_eq0_mutation_rejected : Logic.True := Logic.I.
Print Assumptions big_nat_eq0_mutation_rejected.
