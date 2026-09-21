From mathcomp Require Import ssreflect ssrbool eqtype seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRel.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation.

Inductive RelValidationTrue : SProp := rel_validation_I.
Inductive RelValidationFalse : SProp := .

Definition rel_false_elim (P : SProp) (H : RelValidationFalse) : P :=
  match H return P with end.

Definition RelBoolTruth (b : bool) : SProp :=
  match b with true => RelValidationTrue | false => RelValidationFalse end.

Definition RelBoolRel (bR : bool) (bL : ImportedRel.Bool) : SProp :=
  match bR, bL with
  | true, ImportedRel.Bool_true => RelValidationTrue
  | false, ImportedRel.Bool_false => RelValidationTrue
  | _, _ => RelValidationFalse
  end.

Definition rel_imported_false_ne_true
    (H : Lean.eq ImportedRel.Bool_false ImportedRel.Bool_true) :
    RelValidationFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedRel.Bool_false => RelValidationTrue
    | ImportedRel.Bool_true => RelValidationFalse
    end
  with
  | Lean.eq_refl => rel_validation_I
  end.

Definition rel_bool_prop_to_truth (b : bool) : is_true b -> RelBoolTruth b :=
  match b return is_true b -> RelBoolTruth b with
  | true => fun _ => rel_validation_I
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => RelValidationFalse | false => RelValidationTrue end
      with Logic.eq_refl => rel_validation_I end
  end.

Definition rel_truth_to_strict_bool_prop (b : bool) :
    RelBoolTruth b -> StrictlyInhabited (is_true b) :=
  match b return RelBoolTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => fun H => rel_false_elim _ H
  end.

Fixpoint rel_seq_to_list {T : Type} (xs : seq T) : ImportedRel.List T :=
  match xs with
  | [::] => ImportedRel.List_nil T
  | x :: xs' => ImportedRel.List_cons T x (rel_seq_to_list xs')
  end.

Definition RelListRel {T : Type} (xsR : seq T) (xsL : ImportedRel.List T) : SProp :=
  Lean.eq (rel_seq_to_list xsR) xsL.

Definition rel_imported_eq_sym {T : Type} (x y : T) :
    Lean.eq x y -> Lean.eq y x :=
  fun H => match H in Lean.eq _ z return Lean.eq z x with
           | Lean.eq_refl => @Lean.eq_refl T x
           end.

Definition rel_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedRel.List T) :
    Lean.eq xs ys -> ImportedRel.List_Mem T x xs -> ImportedRel.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedRel.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition rel_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedRel.List T) :
    Logic.eq x y -> ImportedRel.List_Mem T x (ImportedRel.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedRel.List_Mem T x (ImportedRel.List_cons T z xs) with
    | Logic.eq_refl => ImportedRel.List_Mem_head T x xs
    end.

Fixpoint rel_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    RelBoolTruth (x \in xs) -> ImportedRel.List_Mem T x (rel_seq_to_list xs) :=
  match xs as xs0 return
      RelBoolTruth (x \in xs0) -> ImportedRel.List_Mem T x (rel_seq_to_list xs0)
  with
  | [::] => rel_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        RelBoolTruth (b || (x \in ys)) ->
        ImportedRel.List_Mem T x
          (ImportedRel.List_cons T y (rel_seq_to_list ys))
      with
      | ReflectT Hxy => fun _ => rel_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedRel.List_Mem_tail T x y _
          (rel_seq_mem_forward x ys H)
      end
  end.

Definition rel_mem_tail_truth (a b : bool) :
    RelBoolTruth b -> RelBoolTruth (a || b) :=
  match a, b return RelBoolTruth b -> RelBoolTruth (a || b) with
  | true, true => fun _ => rel_validation_I
  | true, false => fun _ => rel_validation_I
  | false, true => fun _ => rel_validation_I
  | false, false => fun H => H
  end.

Definition rel_mem_head_truth (a b : bool) :
    RelBoolTruth a -> RelBoolTruth (a || b) :=
  match a, b return RelBoolTruth a -> RelBoolTruth (a || b) with
  | true, true => fun _ => rel_validation_I
  | true, false => fun _ => rel_validation_I
  | false, true => fun _ => rel_validation_I
  | false, false => fun H => H
  end.

Definition rel_eq_refl_truth (T : eqType) (x : T) : RelBoolTruth (x == x).
Proof. rewrite eqxx. exact rel_validation_I. Defined.

Fixpoint rel_list_to_seq {T : Type} (xs : ImportedRel.List T) : seq T :=
  match xs with
  | ImportedRel.List_nil => [::]
  | ImportedRel.List_cons x xs' => x :: rel_list_to_seq xs'
  end.

Lemma rel_seq_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (rel_list_to_seq (rel_seq_to_list xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Fixpoint rel_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedRel.List T) (H : ImportedRel.List_Mem T x xs) :
    RelBoolTruth (x \in rel_list_to_seq xs) :=
  match H with
  | ImportedRel.List_Mem_head ys =>
      rel_mem_head_truth _ _ (rel_eq_refl_truth T x)
  | ImportedRel.List_Mem_tail y ys Htail =>
      rel_mem_tail_truth _ _ (rel_imported_mem_decoded x ys Htail)
  end.

Definition rel_bool_truth_transport (b1 b2 : bool) :
    Logic.eq b1 b2 -> RelBoolTruth b1 -> RelBoolTruth b2 :=
  fun H Htruth =>
    match H in Logic.eq _ z return RelBoolTruth z with
    | Logic.eq_refl => Htruth
    end.

Definition rel_mem_truth_transport {T : eqType} (x : T) (xs ys : seq T) :
    Logic.eq xs ys -> RelBoolTruth (x \in xs) -> RelBoolTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return RelBoolTruth (x \in zs) with
    | Logic.eq_refl => Htruth
    end.

Definition rel_imported_mem_backward {T : eqType} (x : T) (xs : seq T)
    (H : ImportedRel.List_Mem T x (rel_seq_to_list xs)) :
    RelBoolTruth (x \in xs) :=
  rel_mem_truth_transport x _ _ (rel_seq_roundtrip xs)
    (rel_imported_mem_decoded x (rel_seq_to_list xs) H).

Lemma rel_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedRel.List T) :
  RelListRel xsR xsL ->
  PropSPropRel (x \in xsR)
    (ImportedRel.List_Mem T x xsL).
Proof.
  intro Hlist. apply prop_sprop_rel_intro.
  - intro Hmem. apply (rel_list_mem_transport x _ _ Hlist).
    apply rel_seq_mem_forward. exact (rel_bool_prop_to_truth _ Hmem).
  - intro Hmem.
    have Hcanonical := rel_list_mem_transport x _ _
      (rel_imported_eq_sym _ _ Hlist) Hmem.
    exact (rel_truth_to_strict_bool_prop _
      (rel_imported_mem_backward x xsR Hcanonical)).
Qed.

Lemma rel_bool_true_correspondence (bR : bool) (bL : ImportedRel.Bool) :
  RelBoolRel bR bL -> PropSPropRel (is_true bR)
    (Lean.eq bL ImportedRel.Bool_true).
Proof.
  intro Hrel. apply prop_sprop_rel_intro.
  - destruct bR, bL; cbn in Hrel |- *.
    + exact (rel_false_elim _ Hrel).
    + intros _. exact (@Lean.eq_refl ImportedRel.Bool ImportedRel.Bool_true).
    + intro H. exact (rel_false_elim _ (rel_bool_prop_to_truth false H)).
    + exact (rel_false_elim _ Hrel).
  - destruct bR, bL; cbn in Hrel |- *; intro Heq.
    + exact (rel_false_elim _ Hrel).
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + exact (rel_false_elim _ (rel_imported_false_ne_true Heq)).
    + exact (rel_false_elim _ Hrel).
Qed.

Print Assumptions rel_membership_correspondence.
Print Assumptions rel_bool_true_correspondence.
