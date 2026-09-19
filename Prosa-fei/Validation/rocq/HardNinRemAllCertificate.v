From mathcomp Require Import ssreflect ssrbool eqtype seq.
From LeanImport Require Import Lean.
Require Import ImportedHardCore93 PropSPropFoundation HardCoreCertificates.
From HardSource Require Import Generated_util__list.

Inductive Nin_STrue : SProp := nin_sI.
Inductive Nin_SFalse : SProp := .

Definition NinTruth (b : bool) : SProp :=
  match b with true => Nin_STrue | false => Nin_SFalse end.

Definition nin_coq_false_elim (P : SProp) (H : Logic.False) : P :=
  match H return P with end.

Definition nin_false_to_strict_false (H : False) :
    StrictlyInhabited Logic.False :=
  match H return StrictlyInhabited Logic.False with end.

Definition nin_truth_to_strict (b : bool) :
    NinTruth b -> StrictlyInhabited (is_true b) :=
  match b return NinTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => fun H => match H return StrictlyInhabited (is_true false) with end
  end.

Definition nin_is_true_forward (b : bool) : is_true b -> NinTruth b :=
  match b return is_true b -> NinTruth b with
  | true => fun _ => nin_sI
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with false => Nin_STrue | true => Nin_SFalse end
      with Logic.eq_refl => nin_sI end
  end.

Fixpoint hard_imported_list_to_seq {T : Type} (xs : List T) : seq T :=
  match xs with
  | List_nil => [::]
  | List_cons x xs' => x :: hard_imported_list_to_seq xs'
  end.

Lemma hard_seq_list_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (hard_imported_list_to_seq (hard_seq_to_imported_list xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Definition nin_or_left (a b : bool) : NinTruth a -> NinTruth (a || b) :=
  match a, b return NinTruth a -> NinTruth (a || b) with
  | true, _ => fun _ => nin_sI
  | false, true => fun _ => nin_sI
  | false, false => fun H => H
  end.

Definition nin_or_right (a b : bool) : NinTruth b -> NinTruth (a || b) :=
  match a, b return NinTruth b -> NinTruth (a || b) with
  | true, _ => fun _ => nin_sI
  | false, true => fun _ => nin_sI
  | false, false => fun H => H
  end.

Definition nin_eq_refl_truth (T : eqType) (x : T) : NinTruth (x == x) :=
  match @eqP T x x as r in reflect _ b return NinTruth b with
  | ReflectT _ => nin_sI
  | ReflectF H => nin_coq_false_elim _ (H (Logic.eq_refl x))
  end.

Fixpoint hard_imported_mem_to_decoded_seq {T : eqType} (j : T)
    (xs : List T) (H : List_Mem T j xs) :
    NinTruth (j \in hard_imported_list_to_seq xs) :=
  match H with
  | List_Mem_head ys => nin_or_left _ _ (nin_eq_refl_truth T j)
  | List_Mem_tail y ys Hmem =>
      nin_or_right _ _ (hard_imported_mem_to_decoded_seq j ys Hmem)
  end.

Definition nin_truth_transport {T : eqType} (j : T) (xs ys : seq T) :
    Logic.eq xs ys -> NinTruth (j \in xs) -> NinTruth (j \in ys) :=
  fun Hxy Hmem => match Hxy in Logic.eq _ zs return NinTruth (j \in zs) with
                  | Logic.eq_refl => Hmem
                  end.

Definition hard_imported_mem_to_seq {T : eqType} (j : T) (xs : seq T)
    (H : List_Mem T j (hard_seq_to_imported_list xs)) :
    NinTruth (j \in xs) :=
  nin_truth_transport j _ xs (hard_seq_list_roundtrip xs)
    (hard_imported_mem_to_decoded_seq j _ H).

Definition hard_mem_head {T : Type} (j x : T) (xs : List T) :
    Logic.eq j x -> List_Mem T j (List_cons T x xs) :=
  fun H => match H in Logic.eq _ z return List_Mem T j (List_cons T z xs) with
           | Logic.eq_refl => List_Mem_head T j xs
           end.

Fixpoint hard_seq_mem_forward {T : eqType} (j : T) (xs : seq T) :
    NinTruth (j \in xs) -> List_Mem T j (hard_seq_to_imported_list xs) :=
  match xs as xs0 return NinTruth (j \in xs0) ->
      List_Mem T j (hard_seq_to_imported_list xs0)
  with
  | [::] => fun H => match H with end
  | x :: xs' =>
      match @eqP T j x as r in reflect _ b return
        NinTruth (b || (j \in xs')) ->
        List_Mem T j (List_cons T x (hard_seq_to_imported_list xs'))
      with
      | ReflectT H => fun _ => hard_mem_head j x _ H
      | ReflectF _ => fun H => List_Mem_tail T j x _
          (hard_seq_mem_forward j xs' H)
      end
  end.

Definition nin_imported_mem_transport {T : Type} (j : T)
    (xs ys : List T) : eq xs ys -> List_Mem T j xs -> List_Mem T j ys :=
  fun Hxy Hmem => match Hxy in eq _ zs return List_Mem T j zs with
                  | eq_refl => Hmem
                  end.

Definition original_nin_rem_all_statement
    (T : eqType) (x : T) (xs : seq T) : Prop :=
  ~ (x \in Generated_util__list.rem_all x xs).

Definition imported_nin_rem_all_statement
    (T : eqType) (x : T) (xs : seq T) : SProp :=
  Not (List_Mem T x
    (Prosa_Util_List_rem_all T (hard_decidable_eq T) x
      (hard_seq_to_imported_list xs))).

Definition original_nin_rem_all_has_expected_statement
    (T : eqType) (x : T) (xs : seq T) :
    original_nin_rem_all_statement T x xs :=
  @Generated_util__list.nin_rem_all T x xs.

Definition imported_nin_rem_all_has_expected_statement
    (T : eqType) (x : T) (xs : seq T) :
    imported_nin_rem_all_statement T x xs :=
  Prosa_Util_List_nin_rem_all T (hard_decidable_eq T) x
    (hard_seq_to_imported_list xs).

Theorem nin_rem_all_statement_certificate
    (T : eqType) (x : T) (xs : seq T) :
  PropSPropRel
    (original_nin_rem_all_statement T x xs)
    (imported_nin_rem_all_statement T x xs).
Proof.
  unfold original_nin_rem_all_statement, imported_nin_rem_all_statement.
  apply prop_sprop_rel_intro.
  - intros Hnot Hmem.
    have Hdecoded := nin_imported_mem_transport x _ _
      (hard_imported_eq_sym _ _ (rem_all_recursive_certificate T x xs)) Hmem.
    have Htruth := hard_imported_mem_to_seq x
      (Generated_util__list.rem_all x xs) Hdecoded.
    exact (hard_coq_false_to_imported_false
      (Hnot (interpret_strict _ (nin_truth_to_strict _ Htruth)))).
  - intro Hnot.
    apply strictly_inhabits. intro HmemR.
    exact (interpret_strict _
      (nin_false_to_strict_false
        (Hnot
          (nin_imported_mem_transport x _ _
            (rem_all_recursive_certificate T x xs)
            (hard_seq_mem_forward x
              (Generated_util__list.rem_all x xs)
              (nin_is_true_forward _ HmemR)))))).
Qed.

Print Assumptions nin_rem_all_statement_certificate.
Print Assumptions original_nin_rem_all_has_expected_statement.
Print Assumptions imported_nin_rem_all_has_expected_statement.
