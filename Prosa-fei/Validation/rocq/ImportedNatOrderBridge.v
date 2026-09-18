From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ProcessorStateBridge ImportedNatBridge.
Require Import ImportedListBridge.

Fixpoint imported_zero_le (m : Nat) : Nat_le Nat_zero m :=
  match m with
  | Nat_zero => Lean.Nat_le_refl Nat_zero
  | Nat_succ m' => Lean.Nat_le_step Nat_zero m' (imported_zero_le m')
  end.

Fixpoint imported_le_succ_succ (n m : Nat) (H : Nat_le n m) :
    Nat_le (Nat_succ n) (Nat_succ m) :=
  match H with
  | Lean.Nat_le_refl => Lean.Nat_le_refl (Nat_succ n)
  | Lean.Nat_le_step k H' =>
      Lean.Nat_le_step (Nat_succ n) (Nat_succ k)
        (imported_le_succ_succ n k H')
  end.

Fixpoint imported_le_left_pred (n m : Nat)
    (H : Nat_le (Nat_succ n) m) : Nat_le n m :=
  match H with
  | Lean.Nat_le_refl => Lean.Nat_le_step n n (Lean.Nat_le_refl n)
  | Lean.Nat_le_step k H' =>
      Lean.Nat_le_step n k (imported_le_left_pred n k H')
  end.

Definition imported_le_succ_inv (n m : Nat)
    (H : Nat_le (Nat_succ n) (Nat_succ m)) : Nat_le n m :=
  match H in Nat_le _ z return
    match z with
    | Nat_zero => Validation_STrue
    | Nat_succ k => Nat_le n k
    end
  with
  | Lean.Nat_le_refl => Lean.Nat_le_refl n
  | Lean.Nat_le_step k H' => imported_le_left_pred n k H'
  end.

Definition imported_succ_not_le_zero (n : Nat)
    (H : Nat_le (Nat_succ n) Nat_zero) : Validation_SFalse :=
  match H in Nat_le _ z return
    match z with
    | Nat_zero => Validation_SFalse
    | Nat_succ _ => Validation_STrue
    end
  with
  | Lean.Nat_le_refl => Validation_sI
  | Lean.Nat_le_step _ _ => Validation_sI
  end.

Fixpoint rocq_nat_le_to_imported (n m : nat) :
    RocqBoolTruth (leq n m) ->
    Nat_le (rocq_nat_to_imported n) (rocq_nat_to_imported m) :=
  match n, m return
    RocqBoolTruth (leq n m) ->
    Nat_le (rocq_nat_to_imported n) (rocq_nat_to_imported m)
  with
  | O, m' => fun _ => imported_zero_le (rocq_nat_to_imported m')
  | S n', O => Validation_false_elim _
  | S n', S m' => fun H =>
      imported_le_succ_succ _ _ (rocq_nat_le_to_imported n' m' H)
  end.

Fixpoint imported_nat_le_to_rocq (n m : nat) :
    Nat_le (rocq_nat_to_imported n) (rocq_nat_to_imported m) ->
    RocqBoolTruth (leq n m) :=
  match n, m return
    Nat_le (rocq_nat_to_imported n) (rocq_nat_to_imported m) ->
    RocqBoolTruth (leq n m)
  with
  | O, _ => fun _ => Validation_sI
  | S n', O => imported_succ_not_le_zero (rocq_nat_to_imported n')
  | S n', S m' => fun H =>
      imported_nat_le_to_rocq n' m'
        (imported_le_succ_inv _ _ H)
  end.

Lemma imported_nat_le_bridge (n m : nat) :
  ImportedBoolSPropRel
    (leq n m)
    (Nat_le (rocq_nat_to_imported n) (rocq_nat_to_imported m)).
Proof.
  exact (And_intro _ _
    (rocq_nat_le_to_imported n m)
    (imported_nat_le_to_rocq n m)).
Qed.

Lemma imported_nat_lt_bridge (n m : nat) :
  ImportedBoolSPropRel
    (ltn n m)
    (Nat_lt (rocq_nat_to_imported n) (rocq_nat_to_imported m)).
Proof. exact (imported_nat_le_bridge n.+1 m). Qed.

Definition rocq_and_left_truth (a b : bool) :
    RocqBoolTruth (a && b) -> RocqBoolTruth a :=
  match a, b return RocqBoolTruth (a && b) -> RocqBoolTruth a with
  | true, true => fun _ => Validation_sI
  | true, false => fun _ => Validation_sI
  | false, true => fun H => H
  | false, false => fun H => H
  end.

Definition rocq_and_right_truth (a b : bool) :
    RocqBoolTruth (a && b) -> RocqBoolTruth b :=
  match a, b return RocqBoolTruth (a && b) -> RocqBoolTruth b with
  | true, true => fun _ => Validation_sI
  | true, false => fun H => H
  | false, true => fun _ => Validation_sI
  | false, false => fun H => H
  end.

Definition rocq_and_truth (a b : bool) :
    RocqBoolTruth a -> RocqBoolTruth b -> RocqBoolTruth (a && b) :=
  match a, b return
    RocqBoolTruth a -> RocqBoolTruth b -> RocqBoolTruth (a && b)
  with
  | true, true => fun _ _ => Validation_sI
  | true, false => fun _ H => H
  | false, true => fun H _ => H
  | false, false => fun H _ => H
  end.

Lemma imported_bool_sprop_and_bridge a b p q :
  ImportedBoolSPropRel a p ->
  ImportedBoolSPropRel b q ->
  ImportedBoolSPropRel (a && b) (And p q).
Proof.
  intros Ha Hb.
  destruct Ha as [HaF HaB]. destruct Hb as [HbF HbB].
  apply (And_intro _ _).
  - intro Hab.
    exact (And_intro _ _
      (HaF (rocq_and_left_truth a b Hab))
      (HbF (rocq_and_right_truth a b Hab))).
  - intro Hpq. destruct Hpq as [Hp Hq].
    exact (rocq_and_truth a b (HaB Hp) (HbB Hq)).
Qed.

Print Assumptions imported_nat_le_bridge.
Print Assumptions imported_nat_lt_bridge.
Print Assumptions imported_bool_sprop_and_bridge.
