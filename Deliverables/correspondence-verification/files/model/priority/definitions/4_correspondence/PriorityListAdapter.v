From mathcomp Require Import ssreflect ssrbool eqtype seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityDefinitions.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.
From PriorityCertificates Require Import PriorityBaseAdapter.

Definition PdBoolTruth (b : bool) : SProp :=
  match b with true => PdTrue | false => PdFalse end.

Definition pd_bool_prop_to_truth (b : bool) : is_true b -> PdBoolTruth b :=
  match b return is_true b -> PdBoolTruth b with
  | true => fun _ => pd_true_intro
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => PdFalse | false => PdTrue end
      with Logic.eq_refl => pd_true_intro end
  end.

Definition pd_truth_to_strict_bool_prop (b : bool) :
    PdBoolTruth b -> StrictlyInhabited (is_true b) :=
  match b return PdBoolTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => fun H => match H with end
  end.

Fixpoint pd_seq_to_list {T : Type} (xs : seq T) :
    ImportedPriorityDefinitions.List T :=
  match xs with
  | [::] => ImportedPriorityDefinitions.List_nil T
  | x :: xs' => ImportedPriorityDefinitions.List_cons T x (pd_seq_to_list xs')
  end.

Fixpoint pd_list_to_seq {T : Type} (xs : ImportedPriorityDefinitions.List T) :
    seq T :=
  match xs with
  | ImportedPriorityDefinitions.List_nil => [::]
  | ImportedPriorityDefinitions.List_cons x xs' => x :: pd_list_to_seq xs'
  end.

Definition PdListRel {T : Type} (xsR : seq T)
    (xsL : ImportedPriorityDefinitions.List T) : SProp :=
  Lean.eq (pd_seq_to_list xsR) xsL.

Lemma pd_seq_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (pd_list_to_seq (pd_seq_to_list xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma pd_list_roundtrip {T : Type} (xs : ImportedPriorityDefinitions.List T) :
  Lean.eq (pd_seq_to_list (pd_list_to_seq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr
      (ImportedPriorityDefinitions.List_cons T x) _ _ IH).
Qed.

Definition pd_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedPriorityDefinitions.List T) :
  Lean.eq xs ys -> ImportedPriorityDefinitions.List_Mem T x xs ->
  ImportedPriorityDefinitions.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return
      ImportedPriorityDefinitions.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition pd_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedPriorityDefinitions.List T) :
  Logic.eq x y ->
  ImportedPriorityDefinitions.List_Mem T x
    (ImportedPriorityDefinitions.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedPriorityDefinitions.List_Mem T x
        (ImportedPriorityDefinitions.List_cons T z xs) with
    | Logic.eq_refl => ImportedPriorityDefinitions.List_Mem_head T x xs
    end.

Definition pd_mem_head_truth (a b : bool) :
  PdBoolTruth a -> PdBoolTruth (a || b) :=
  match a, b return PdBoolTruth a -> PdBoolTruth (a || b) with
  | true, true => fun _ => pd_true_intro
  | true, false => fun _ => pd_true_intro
  | false, true => fun H => match H with end
  | false, false => fun H => H
  end.

Definition pd_mem_tail_truth (a b : bool) :
  PdBoolTruth b -> PdBoolTruth (a || b) :=
  match a, b return PdBoolTruth b -> PdBoolTruth (a || b) with
  | true, true => fun _ => pd_true_intro
  | true, false => fun H => match H with end
  | false, true => fun _ => pd_true_intro
  | false, false => fun H => H
  end.

Definition pd_eq_refl_truth (T : eqType) (x : T) : PdBoolTruth (x == x).
Proof. rw eqxx. exact pd_true_intro. Defined.

Fixpoint pd_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    PdBoolTruth (x \in xs) ->
    ImportedPriorityDefinitions.List_Mem T x (pd_seq_to_list xs) :=
  match xs as zs return PdBoolTruth (x \in zs) ->
      ImportedPriorityDefinitions.List_Mem T x (pd_seq_to_list zs) with
  | [::] => fun H => match H with end
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        PdBoolTruth (b || (x \in ys)) ->
        ImportedPriorityDefinitions.List_Mem T x
          (ImportedPriorityDefinitions.List_cons T y (pd_seq_to_list ys)) with
      | ReflectT Hxy => fun _ => pd_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H =>
          ImportedPriorityDefinitions.List_Mem_tail T x y _
            (pd_seq_mem_forward x ys H)
      end
  end.

Fixpoint pd_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedPriorityDefinitions.List T)
    (H : ImportedPriorityDefinitions.List_Mem T x xs) :
    PdBoolTruth (x \in pd_list_to_seq xs) :=
  match H with
  | ImportedPriorityDefinitions.List_Mem_head ys =>
      pd_mem_head_truth _ _ (pd_eq_refl_truth T x)
  | ImportedPriorityDefinitions.List_Mem_tail y ys Htail =>
      pd_mem_tail_truth _ _ (pd_imported_mem_decoded x ys Htail)
  end.

Definition pd_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) :
  Logic.eq xs ys -> PdBoolTruth (x \in xs) -> PdBoolTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return PdBoolTruth (x \in zs) with
    | Logic.eq_refl => Htruth
    end.

Lemma pd_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedPriorityDefinitions.List T) :
  PdListRel xsR xsL ->
  PropSPropRel (x \in xsR) (ImportedPriorityDefinitions.List_Mem T x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. apply (pd_list_mem_transport x _ _ Hxs).
    apply pd_seq_mem_forward. exact (pd_bool_prop_to_truth _ Hmem).
  - intro Hmem.
    apply pd_truth_to_strict_bool_prop.
    apply (pd_mem_truth_transport x _ _ (pd_seq_roundtrip xsR)).
    apply pd_imported_mem_decoded.
    exact (pd_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Print Assumptions pd_seq_roundtrip.
Print Assumptions pd_list_roundtrip.
Print Assumptions pd_membership_correspondence.
