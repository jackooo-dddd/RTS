From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ProcessorStateBridge EqTypeBridge.

Fixpoint seq_to_imported_list {T : Type} (xs : seq T) : List_inst1 T :=
  match xs with
  | [::] => List_nil_inst1 T
  | x :: xs' => List_cons_inst1 T x (seq_to_imported_list xs')
  end.

Fixpoint imported_list_to_seq {T : Type} (xs : List_inst1 T) : seq T :=
  match xs with
  | List_nil_inst1 => [::]
  | List_cons_inst1 x xs' => x :: imported_list_to_seq xs'
  end.

Definition ImportedListRel {T : Type} (xsR : seq T)
    (xsL : List_inst1 T) : SProp :=
  eq (seq_to_imported_list xsR) xsL.

Definition imported_list_congr_of_seq_eq {T : Type} (xs ys : seq T) :
    Logic.eq xs ys ->
    eq (seq_to_imported_list xs) (seq_to_imported_list ys) :=
  fun H =>
    match H in Logic.eq _ zs return
      eq (seq_to_imported_list xs) (seq_to_imported_list zs)
    with
    | Logic.eq_refl => eq_refl (seq_to_imported_list xs)
    end.

Lemma seq_list_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (imported_list_to_seq (seq_to_imported_list xs)) xs.
Proof.
  induction xs; cbn.
  - reflexivity.
  - f_equal. exact IHxs.
Qed.

Definition imported_list_cons_congr {T : Type} (x : T)
    (xs ys : List_inst1 T) :
    eq xs ys ->
    eq (List_cons_inst1 T x xs) (List_cons_inst1 T x ys) :=
  fun H =>
    match H in eq _ zs return
      eq (List_cons_inst1 T x xs) (List_cons_inst1 T x zs)
    with
    | eq_refl => eq_refl (List_cons_inst1 T x xs)
    end.

Lemma imported_list_roundtrip {T : Type} (xs : List_inst1 T) :
  eq (seq_to_imported_list (imported_list_to_seq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (eq_refl (List_nil_inst1 T)).
  - exact (imported_list_cons_congr x _ _ IH).
Qed.

Definition ImportedBoolSPropRel (b : bool) (p : SProp) : SProp :=
  And (RocqBoolTruth b -> p) (p -> RocqBoolTruth b).

Definition rocq_or_left_truth (a b : bool) :
    RocqBoolTruth a -> RocqBoolTruth (a || b) :=
  match a, b return RocqBoolTruth a -> RocqBoolTruth (a || b) with
  | true, true => fun _ => Validation_sI
  | true, false => fun _ => Validation_sI
  | false, true => fun _ => Validation_sI
  | false, false => fun H => H
  end.

Definition rocq_or_right_truth (a b : bool) :
    RocqBoolTruth b -> RocqBoolTruth (a || b) :=
  match a, b return RocqBoolTruth b -> RocqBoolTruth (a || b) with
  | true, true => fun _ => Validation_sI
  | true, false => fun _ => Validation_sI
  | false, true => fun _ => Validation_sI
  | false, false => fun H => H
  end.

Definition imported_mem_head_of_coq_eq {T : Type} (j x : T)
    (xs : List_inst1 T) :
    Logic.eq j x ->
    List_Mem_inst1 T j (List_cons_inst1 T x xs) :=
  fun H =>
    match H in Logic.eq _ z return
      List_Mem_inst1 T j (List_cons_inst1 T z xs)
    with
    | Logic.eq_refl => List_Mem_head_inst1 T j xs
    end.

Fixpoint seq_mem_to_imported {T : eqType} (j : T) (xs : seq T) :
    RocqBoolTruth (j \in xs) ->
    List_Mem_inst1 T j (seq_to_imported_list xs) :=
  match xs as xs0 return
    RocqBoolTruth (j \in xs0) ->
    List_Mem_inst1 T j (seq_to_imported_list xs0)
  with
  | [::] => Validation_false_elim _
  | x :: xs' =>
      match @eqP T j x as r in reflect _ b return
        RocqBoolTruth (b || (j \in xs')) ->
        List_Mem_inst1 T j
          (List_cons_inst1 T x (seq_to_imported_list xs'))
      with
      | ReflectT H => fun _ =>
          imported_mem_head_of_coq_eq j x (seq_to_imported_list xs') H
      | ReflectF _ => fun H =>
          List_Mem_tail_inst1 T j x (seq_to_imported_list xs')
            (seq_mem_to_imported j xs' H)
      end
  end.

Fixpoint imported_mem_to_decoded_seq {T : eqType} (j : T)
    (xs : List_inst1 T) (H : List_Mem_inst1 T j xs) :
    RocqBoolTruth (j \in imported_list_to_seq xs) :=
  match H with
  | List_Mem_head_inst1 ys =>
      rocq_or_left_truth _ _ (eqtype_refl_truth T j)
  | List_Mem_tail_inst1 y ys Hmem =>
      rocq_or_right_truth _ _
        (imported_mem_to_decoded_seq j ys Hmem)
  end.

Definition rocq_mem_truth_transport {T : eqType} (j : T)
    (xs ys : seq T) :
    Logic.eq xs ys -> RocqBoolTruth (j \in xs) -> RocqBoolTruth (j \in ys) :=
  fun Hxy Hmem =>
    match Hxy in Logic.eq _ zs return RocqBoolTruth (j \in zs) with
    | Logic.eq_refl => Hmem
    end.

Definition imported_mem_to_seq {T : eqType} (j : T) (xs : seq T)
    (H : List_Mem_inst1 T j (seq_to_imported_list xs)) :
    RocqBoolTruth (j \in xs) :=
  rocq_mem_truth_transport j
    (imported_list_to_seq (seq_to_imported_list xs)) xs
    (seq_list_roundtrip xs)
    (imported_mem_to_decoded_seq j (seq_to_imported_list xs) H).

Definition imported_mem_transport {T : Type} (j : T)
    (xs ys : List_inst1 T) :
    eq xs ys -> List_Mem_inst1 T j xs -> List_Mem_inst1 T j ys :=
  fun Hxy Hmem =>
    match Hxy in eq _ zs return List_Mem_inst1 T j zs with
    | eq_refl => Hmem
    end.

Lemma seq_membership_bridge (T : eqType) (j : T) (xs : seq T) :
  ImportedBoolSPropRel
    (j \in xs)
    (List_Mem_inst1 T j (seq_to_imported_list xs)).
Proof.
  exact (And_intro _ _
    (seq_mem_to_imported j xs)
    (imported_mem_to_seq j xs)).
Qed.

Lemma seq_membership_related_bridge (T : eqType) (j : T)
    (xs : seq T) (ys : List_inst1 T) :
  ImportedListRel xs ys ->
  ImportedBoolSPropRel (j \in xs) (List_Mem_inst1 T j ys).
Proof.
  intro Hlist.
  apply (And_intro _ _).
  - intro Hmem.
    exact (imported_mem_transport j _ _ Hlist
      (seq_mem_to_imported j xs Hmem)).
  - intro Hmem.
    exact (imported_mem_to_seq j xs
      (imported_mem_transport j _ _
        (imported_eq_sym _ _ Hlist) Hmem)).
Qed.

Print Assumptions seq_list_roundtrip.
Print Assumptions imported_list_roundtrip.
Print Assumptions seq_membership_bridge.
Print Assumptions seq_membership_related_bridge.
