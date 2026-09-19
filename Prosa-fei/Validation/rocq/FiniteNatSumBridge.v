From mathcomp Require Import ssreflect ssrbool ssrnat seq bigop.
From LeanImport Require Import Lean.
Require Import ImportedFiniteNatSumNormalized93 PropSPropFoundation HardSumCertificate.

Definition imported_one : Nat :=
  OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1).

Lemma imported_one_is_succ_zero : eq imported_one (Nat_succ Nat_zero).
Proof. exact (eq_refl _). Qed.

Lemma imported_add_zero (n : Nat) :
  eq (Nat_add n Nat_zero) n.
Proof. exact (eq_refl _). Qed.

Lemma imported_add_succ (n m : Nat) :
  eq (Nat_add n (Nat_succ m)) (Nat_succ (Nat_add n m)).
Proof. exact (eq_refl _). Qed.

Lemma imported_add_succ_prop (n m : Nat) :
  Logic.eq (Nat_add n (Nat_succ m)) (Nat_succ (Nat_add n m)).
Proof. reflexivity. Qed.

Lemma imported_sub_zero (n : Nat) :
  eq (Nat_sub n Nat_zero) n.
Proof. exact (eq_refl _). Qed.

Lemma imported_sub_succ (n m : Nat) :
  eq (Nat_sub n (Nat_succ m)) (Nat_pred (Nat_sub n m)).
Proof. exact (eq_refl _). Qed.

Lemma imported_sub_succ_prop (n m : Nat) :
  Logic.eq (Nat_sub n (Nat_succ m)) (Nat_pred (Nat_sub n m)).
Proof. reflexivity. Qed.

Lemma imported_pred_zero : eq (Nat_pred Nat_zero) Nat_zero.
Proof. exact (eq_refl _). Qed.

Lemma imported_pred_succ (n : Nat) : eq (Nat_pred (Nat_succ n)) n.
Proof. exact (eq_refl _). Qed.

Definition imported_eq_congr {A B : Type} (f : A -> B) (x y : A) :
    eq x y -> eq (f x) (f y) :=
  fun H => match H in eq _ z return eq (f x) (f z) with
           | eq_refl => eq_refl _
           end.

Lemma imported_range_zero (start step : Nat) :
  eq (List_range' start Nat_zero step) (List_nil_inst1 Nat).
Proof. exact (eq_refl _). Qed.

Lemma imported_range_succ (start len step : Nat) :
  eq (List_range' start (Nat_succ len) step)
     (List_cons_inst1 Nat start (List_range' (Nat_add start step) len step)).
Proof. exact (eq_refl _). Qed.

Lemma imported_range_succ_prop (start len step : Nat) :
  Logic.eq (List_range' start (Nat_succ len) step)
     (List_cons_inst1 Nat start (List_range' (Nat_add start step) len step)).
Proof. reflexivity. Qed.

Lemma imported_map_nil {A B : Type} (f : A -> B) :
  eq (List_map_inst3 A B f (List_nil_inst1 A)) (List_nil_inst1 B).
Proof. exact (eq_refl _). Qed.

Lemma imported_map_cons {A B : Type} (f : A -> B) (x : A)
    (xs : List_inst1 A) :
  eq (List_map_inst3 A B f (List_cons_inst1 A x xs))
     (List_cons_inst1 B (f x) (List_map_inst3 A B f xs)).
Proof. exact (eq_refl _). Qed.

Lemma imported_map_cons_prop {A B : Type} (f : A -> B) (x : A)
    (xs : List_inst1 A) :
  Logic.eq (List_map_inst3 A B f (List_cons_inst1 A x xs))
     (List_cons_inst1 B (f x) (List_map_inst3 A B f xs)).
Proof. reflexivity. Qed.

Lemma imported_foldr_nil {A B : Type} (f : A -> B -> B) (z : B) :
  eq (List_foldr_inst3 A B f z (List_nil_inst1 A)) z.
Proof. exact (eq_refl _). Qed.

Lemma imported_foldr_cons {A B : Type} (f : A -> B -> B) (z : B)
    (x : A) (xs : List_inst1 A) :
  eq (List_foldr_inst3 A B f z (List_cons_inst1 A x xs))
     (f x (List_foldr_inst3 A B f z xs)).
Proof. exact (eq_refl _). Qed.

Definition imported_list_sum (xs : List_inst1 Nat) : Nat :=
  List_foldr_inst3 Nat Nat Nat_add Nat_zero xs.

Lemma imported_list_sum_nil :
  eq (imported_list_sum (List_nil_inst1 Nat)) Nat_zero.
Proof. exact (eq_refl _). Qed.

Lemma imported_list_sum_cons (x : Nat) (xs : List_inst1 Nat) :
  eq (imported_list_sum (List_cons_inst1 Nat x xs))
     (Nat_add x (imported_list_sum xs)).
Proof. exact (eq_refl _). Qed.

Lemma imported_list_sum_cons_prop (x : Nat) (xs : List_inst1 Nat) :
  Logic.eq (imported_list_sum (List_cons_inst1 Nat x xs))
     (Nat_add x (imported_list_sum xs)).
Proof. reflexivity. Qed.

Lemma imported_add_canonical (a b : nat) :
  eq (Nat_add (sum_nat_to_imported a) (sum_nat_to_imported b))
     (sum_nat_to_imported (a + b)).
Proof.
  induction b as [|b IH].
  - rewrite addn0. exact (eq_refl _).
  - rewrite addnS. cbn [sum_nat_to_imported].
    exact (match IH in eq _ z return
      eq (Nat_succ (Nat_add (sum_nat_to_imported a) (sum_nat_to_imported b)))
         (Nat_succ z)
    with eq_refl => eq_refl _ end).
Qed.

Lemma imported_add_one_canonical (a : nat) :
  eq (Nat_add (sum_nat_to_imported a) imported_one)
     (sum_nat_to_imported a.+1).
Proof. exact (eq_refl _). Qed.

Lemma imported_pred_canonical (a : nat) :
  eq (Nat_pred (sum_nat_to_imported a))
     (sum_nat_to_imported a.-1).
Proof. destruct a; exact (eq_refl _). Qed.

Fixpoint imported_zero_sub (b : nat) :
    eq (Nat_sub Nat_zero (sum_nat_to_imported b)) Nat_zero :=
  match b with
  | O => eq_refl _
  | S b' => sum_eq_trans _ _ _
      (imported_sub_succ Nat_zero (sum_nat_to_imported b'))
      (sum_eq_trans _ _ _
        (imported_eq_congr Nat_pred _ _ (imported_zero_sub b'))
        imported_pred_zero)
  end.

Fixpoint imported_succ_sub_succ (b : nat) : forall a : nat,
    eq (Nat_sub (Nat_succ (sum_nat_to_imported a))
          (Nat_succ (sum_nat_to_imported b)))
       (Nat_sub (sum_nat_to_imported a) (sum_nat_to_imported b)) :=
  match b as b0 return forall a : nat,
      eq (Nat_sub (Nat_succ (sum_nat_to_imported a))
            (Nat_succ (sum_nat_to_imported b0)))
         (Nat_sub (sum_nat_to_imported a) (sum_nat_to_imported b0))
  with
  | O => fun a => eq_refl _
  | S b' => fun a =>
      imported_eq_congr Nat_pred _ _ (imported_succ_sub_succ b' a)
  end.

Fixpoint imported_sub_canonical (b : nat) : forall a : nat,
    eq (Nat_sub (sum_nat_to_imported a) (sum_nat_to_imported b))
       (sum_nat_to_imported (a - b)) :=
  match b as b0 return forall a : nat,
      eq (Nat_sub (sum_nat_to_imported a) (sum_nat_to_imported b0))
         (sum_nat_to_imported (a - b0))
  with
  | O => fun a =>
      match a as a0 return
        eq (Nat_sub (sum_nat_to_imported a0) Nat_zero)
           (sum_nat_to_imported (a0 - O))
      with
      | O => eq_refl _
      | S a' => eq_refl _
      end
  | S b' => fun a =>
      match a as a0 return
        eq (Nat_sub (sum_nat_to_imported a0)
              (Nat_succ (sum_nat_to_imported b')))
           (sum_nat_to_imported (a0 - S b'))
      with
      | O => imported_zero_sub (S b')
      | S a' => sum_eq_trans _ _ _
          (imported_succ_sub_succ b' a')
          (imported_sub_canonical b' a')
      end
  end.

Fixpoint seq_nat_to_imported (xs : seq nat) : List_inst1 Nat :=
  match xs with
  | [::] => List_nil_inst1 Nat
  | x :: xs' => List_cons_inst1 Nat (sum_nat_to_imported x)
      (seq_nat_to_imported xs')
  end.

Lemma imported_range_iota_prop (start len : nat) :
  Logic.eq (List_range' (sum_nat_to_imported start) (sum_nat_to_imported len)
        imported_one)
     (seq_nat_to_imported (iota start len)).
Proof.
  elim: len start => [|len IH] start.
  - reflexivity.
  - cbn [sum_nat_to_imported iota seq_nat_to_imported].
    rewrite imported_range_succ_prop.
    have Hstart : Logic.eq
        (Nat_add (sum_nat_to_imported start) imported_one)
        (sum_nat_to_imported start.+1) by reflexivity.
    rewrite Hstart (IH start.+1). reflexivity.
Qed.

Lemma imported_map_converted_prop (F : nat -> nat) (xs : seq nat) :
  Logic.eq (List_map_inst3 Nat Nat (canonical_imported_function F)
        (seq_nat_to_imported xs))
     (seq_nat_to_imported (map F xs)).
Proof.
  elim: xs => [|x xs IH].
  - reflexivity.
  - cbn [seq_nat_to_imported].
    rewrite imported_map_cons_prop.
    unfold canonical_imported_function.
    rewrite sum_rocq_roundtrip IH. reflexivity.
Qed.

Lemma imported_add_canonical_prop (a b : nat) :
  Logic.eq (Nat_add (sum_nat_to_imported a) (sum_nat_to_imported b))
     (sum_nat_to_imported (a + b)).
Proof.
  induction b as [|b IH].
  - rewrite addn0. reflexivity.
  - rewrite addnS. cbn [sum_nat_to_imported].
    rewrite imported_add_succ_prop IH. reflexivity.
Qed.

Lemma imported_sub_canonical_prop (a b : nat) :
  Logic.eq (Nat_sub (sum_nat_to_imported a) (sum_nat_to_imported b))
     (sum_nat_to_imported (a - b)).
Proof.
  induction b as [|b IH].
  - rewrite subn0. reflexivity.
  - rewrite subnS. cbn [sum_nat_to_imported].
    rewrite imported_sub_succ_prop IH. destruct (a - b); reflexivity.
Qed.

Lemma imported_list_sum_converted_prop (xs : seq nat) :
  Logic.eq (imported_list_sum (seq_nat_to_imported xs))
     (sum_nat_to_imported (foldr addn O xs)).
Proof.
  elim: xs => [|x xs IH].
  - reflexivity.
  - cbn [seq_nat_to_imported foldr]. rewrite imported_list_sum_cons_prop IH.
    exact (imported_add_canonical_prop x (foldr addn O xs)).
Qed.

Lemma imported_interval_sum_unfold_prop (m n : nat) (F : nat -> nat) :
  Logic.eq (imported_interval_sum m n F)
     (imported_list_sum
       (List_map_inst3 Nat Nat (canonical_imported_function F)
         (List_range' (sum_nat_to_imported m)
           (Nat_sub (sum_nat_to_imported n) (sum_nat_to_imported m))
           imported_one))).
Proof. reflexivity. Qed.

Lemma mathcomp_big_seq_as_fold (xs : seq nat) (F : nat -> nat) :
  Logic.eq (\sum_(i <- xs) F i) (foldr addn O (map F xs)).
Proof.
  elim: xs => [|x xs IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons. cbn [map foldr]. now rewrite IH.
Qed.

Lemma finite_nat_sum_value_bridge_prop (m n : nat) (F : nat -> nat) :
  Logic.eq (imported_interval_sum m n F)
    (sum_nat_to_imported (\sum_(m <= i < n) F i)).
Proof.
  rewrite imported_interval_sum_unfold_prop.
  rewrite imported_sub_canonical_prop.
  rewrite imported_range_iota_prop.
  rewrite imported_map_converted_prop.
  rewrite imported_list_sum_converted_prop.
  rewrite /index_iota mathcomp_big_seq_as_fold.
  reflexivity.
Qed.

Theorem finite_nat_sum_value_bridge_closed (m n : nat) (F : nat -> nat) :
  FiniteNatSumValueBridge m n F.
Proof.
  exact (coq_eq_to_imported_eq _ _
    (finite_nat_sum_value_bridge_prop m n F)).
Qed.

Theorem big_nat_eq0_closed_certificate (m n : nat) (F : nat -> nat) :
  PropSPropRel
    (source_big_nat_eq0_statement m n F)
    (imported_big_nat_eq0_statement m n F).
Proof.
  exact (big_nat_eq0_parametric_certificate m n F
    (finite_nat_sum_value_bridge_closed m n F)).
Qed.

Print Assumptions imported_range_succ.
Print Assumptions finite_nat_sum_value_bridge_closed.
Print Assumptions big_nat_eq0_closed_certificate.
