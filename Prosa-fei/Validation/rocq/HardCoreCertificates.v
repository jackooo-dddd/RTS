From mathcomp Require Import ssreflect ssrbool eqtype seq.
From prosa Require Import model.processor.spin.
From LeanImport Require Import Lean.
Require Import ImportedHardCore93.
Require Import PropSPropFoundation.
From HardSource Require Import Generated_util__list.

Inductive Hard_STrue : SProp := hard_sI.
Inductive Hard_SFalse : SProp := .

Definition hard_false_elim (P : SProp) (H : Hard_SFalse) : P :=
  match H return P with end.

Definition hard_imported_false_elim (P : SProp) (H : False) : P :=
  match H return P with end.

Definition HardBoolRel (bR : bool) (bL : Bool) : SProp :=
  match bR, bL with
  | true, Bool_true => Hard_STrue
  | false, Bool_false => Hard_STrue
  | _, _ => Hard_SFalse
  end.

Definition hard_coq_false_to_imported_false (H : Logic.False) : False :=
  match H return False with end.

Definition hard_decidable_eq (T : eqType) : DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => Decidable_isTrue (eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => Decidable_isFalse (eq x y)
        (fun imported_H => hard_coq_false_to_imported_false
          (H (imported_eq_to_coq_eq x y imported_H)))
    end.

Lemma hard_eqtype_bool_bridge (T : eqType) (x y : T) :
  HardBoolRel (x == y)
    (Decidable_decide (eq x y) (hard_decidable_eq T x y)).
Proof.
  unfold hard_decidable_eq.
  destruct (@eqP T x y); cbn; exact hard_sI.
Qed.

Inductive SpinStateRel (Job : eqType) :
    prosa.model.processor.spin.processor_state Job ->
    Prosa_Model_Processor_Spin_processor_state Job -> SProp :=
| spin_state_idle : SpinStateRel Job
    (prosa.model.processor.spin.Idle Job)
    (Prosa_Model_Processor_Spin_processor_state_Idle Job)
| spin_state_spin (j : Job) : SpinStateRel Job
    (prosa.model.processor.spin.Spin Job j)
    (Prosa_Model_Processor_Spin_processor_state_Spin Job j)
| spin_state_progress (j : Job) : SpinStateRel Job
    (prosa.model.processor.spin.Progress Job j)
    (Prosa_Model_Processor_Spin_processor_state_Progress Job j).

Theorem spin_idle_constructor_certificate (Job : eqType) :
  SpinStateRel Job (prosa.model.processor.spin.Idle Job)
    (Prosa_Model_Processor_Spin_processor_state_Idle Job).
Proof. constructor. Qed.

Theorem spin_spin_constructor_certificate (Job : eqType) (j : Job) :
  SpinStateRel Job (prosa.model.processor.spin.Spin Job j)
    (Prosa_Model_Processor_Spin_processor_state_Spin Job j).
Proof. constructor. Qed.

Theorem spin_progress_constructor_certificate (Job : eqType) (j : Job) :
  SpinStateRel Job (prosa.model.processor.spin.Progress Job j)
    (Prosa_Model_Processor_Spin_processor_state_Progress Job j).
Proof. constructor. Qed.

Theorem spin_scheduled_on_certificate (Job : eqType) (jR jL : Job)
    (sR : prosa.model.processor.spin.processor_state Job)
    (sL : Prosa_Model_Processor_Spin_processor_state Job) :
  Logic.eq jR jL -> SpinStateRel Job sR sL ->
  HardBoolRel
    (prosa.model.processor.spin.spin_scheduled_on Job jR sR tt)
    (Prosa_Model_Processor_Spin_processor_state_spin_scheduled_on
       Job (hard_decidable_eq Job) jL sL Unit_unit).
Proof.
  intros Hjob Hstate. destruct Hjob. destruct Hstate as [|k|k]; cbn.
  - exact hard_sI.
  - exact (hard_eqtype_bool_bridge Job k jR).
  - exact (hard_eqtype_bool_bridge Job k jR).
Qed.

Fixpoint hard_seq_to_imported_list {T : Type} (xs : seq T) : List T :=
  match xs with
  | [::] => List_nil T
  | x :: xs' => List_cons T x (hard_seq_to_imported_list xs')
  end.

Definition hard_list_cons_congr {T : Type} (x : T)
    (xs ys : List T) :
    eq xs ys -> eq (List_cons T x xs) (List_cons T x ys) :=
  fun H => match H in eq _ zs return
    eq (List_cons T x xs) (List_cons T x zs)
  with
  | eq_refl => eq_refl (List_cons T x xs)
  end.

Definition hard_imported_eq_sym {T : Type} (x y : T) : eq x y -> eq y x :=
  fun H => match H in eq _ z return eq z x with
           | eq_refl => eq_refl x
           end.

Definition hard_imported_eq_trans {T : Type} (x y z : T) :
    eq x y -> eq y z -> eq x z :=
  fun Hxy Hyz =>
    match Hxy in eq _ y0 return eq y0 z -> eq x z with
    | eq_refl => fun H => H
    end Hyz.

Definition hard_imported_ite_true {A : Type} (p : SProp)
    (d : Decidable p) (hp : p) (x y : A) :
    eq (ite A p d x y) x :=
  match d as d0 return eq (ite A p d0 x y) x with
  | Decidable_isFalse hn => hard_imported_false_elim _ (hn hp)
  | Decidable_isTrue _ => eq_refl x
  end.

Definition hard_imported_ite_false {A : Type} (p : SProp)
    (d : Decidable p) (hn : Not p) (x y : A) :
    eq (ite A p d x y) y :=
  match d as d0 return eq (ite A p d0 x y) y with
  | Decidable_isFalse _ => eq_refl y
  | Decidable_isTrue hp => hard_imported_false_elim _ (hn hp)
  end.

Lemma hard_imported_rem_all_nil (T : eqType) (x : T) :
  eq (Prosa_Util_List_rem_all T (hard_decidable_eq T) x (List_nil T))
     (List_nil T).
Proof. exact (eq_refl (List_nil T)). Qed.

Lemma hard_imported_rem_all_cons (T : eqType) (x a : T) (xs : List T) :
  eq
    (Prosa_Util_List_rem_all T (hard_decidable_eq T) x
       (List_cons T a xs))
    (ite (List T) (eq a x) (hard_decidable_eq T a x)
       (Prosa_Util_List_rem_all T (hard_decidable_eq T) x xs)
       (List_cons T a
         (Prosa_Util_List_rem_all T (hard_decidable_eq T) x xs))).
Proof. exact (eq_refl _). Qed.

Theorem rem_all_recursive_certificate (T : eqType) (x : T) (xs : seq T) :
  eq
    (hard_seq_to_imported_list (Generated_util__list.rem_all x xs))
    (Prosa_Util_List_rem_all T (hard_decidable_eq T) x
       (hard_seq_to_imported_list xs)).
Proof.
  induction xs as [|a xs IH].
  - cbn [Generated_util__list.rem_all hard_seq_to_imported_list
         Prosa_Util_List_rem_all List_brecOn
         Prosa_Util_List_rem_all__f].
    exact (eq_refl (List_nil T)).
	  - unfold Prosa_Util_List_rem_all in IH.
	    unfold List_brecOn in IH.
	    unfold List_brecOn_go in IH.
    unfold Prosa_Util_List_rem_all__f in IH.
    cbn in IH.
    cbn [Generated_util__list.rem_all hard_seq_to_imported_list
         Prosa_Util_List_rem_all List_brecOn
         Prosa_Util_List_rem_all__f].
    destruct (@eqP T a x) as [Heq|Hneq]; cbn.
    +
      exact (hard_imported_eq_trans _ _ _ IH
        (hard_imported_eq_sym _ _
          (hard_imported_ite_true (eq a x) (hard_decidable_eq T a x)
            (coq_eq_to_imported_eq a x Heq) _ _))).
    +
      have Hcons := hard_list_cons_congr a _ _ IH.
      exact (hard_imported_eq_trans _ _ _ Hcons
        (hard_imported_eq_sym _ _
          (hard_imported_ite_false (eq a x) (hard_decidable_eq T a x)
            (fun HeqL => hard_coq_false_to_imported_false
              (Hneq (imported_eq_to_coq_eq a x HeqL))) _ _))).
Qed.

(* The theorem-level membership bridge below is retained as work in progress.
   It is deliberately excluded from the checked certificate module until its
   dependent [List.Mem] elimination is completed.  The recursive definition
   certificate above is independent and closed. *)
(*
Definition HardBoolTruth (b : bool) : SProp :=
  match b with true => Hard_STrue | false => Hard_SFalse end.

Definition hard_is_true_to_truth (b : bool) : is_true b -> HardBoolTruth b :=
  fun H =>
    match Logic.eq_sym H in Logic.eq _ b0 return HardBoolTruth b0 with
    | Logic.eq_refl => hard_sI
    end.

Definition hard_truth_to_strict_is_true (b : bool) :
    HardBoolTruth b -> StrictlyInhabited (is_true b) :=
  match b return HardBoolTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => hard_false_elim _
  end.

Definition hard_imported_mem_transport {T : Type} (j : T)
    (xs ys : List T) :
    eq xs ys -> List_Mem T j xs -> List_Mem T j ys :=
  fun Hxy Hmem =>
    match Hxy in eq _ zs return List_Mem T j zs with
    | eq_refl => Hmem
    end.

Definition hard_imported_mem_head {T : Type} (j x : T)
    (xs : List T) :
    Logic.eq j x -> List_Mem T j (List_cons T x xs) :=
  fun H => match H in Logic.eq _ z return
    List_Mem T j (List_cons T z xs)
  with
  | Logic.eq_refl => List_Mem_head T j xs
  end.

Definition hard_truth_or_left (a b : bool) :
    HardBoolTruth a -> HardBoolTruth (a || b) :=
  match a, b return HardBoolTruth a -> HardBoolTruth (a || b) with
  | true, _ => fun _ => hard_sI
  | false, true => fun _ => hard_sI
  | false, false => fun H => H
  end.

Definition hard_truth_or_right (a b : bool) :
    HardBoolTruth b -> HardBoolTruth (a || b) :=
  match a, b return HardBoolTruth b -> HardBoolTruth (a || b) with
  | true, true => fun _ => hard_sI
  | true, false => fun _ => hard_sI
  | false, true => fun _ => hard_sI
  | false, false => fun H => H
  end.

Fixpoint hard_seq_mem_to_imported {T : eqType} (j : T) (xs : seq T) :
    HardBoolTruth (j \in xs) ->
    List_Mem T j (hard_seq_to_imported_list xs) :=
  match xs as xs0 return HardBoolTruth (j \in xs0) ->
      List_Mem T j (hard_seq_to_imported_list xs0)
  with
  | [::] => hard_false_elim _
  | x :: xs' =>
      match @eqP T j x as r in reflect _ b return
        HardBoolTruth (b || (j \in xs')) ->
        List_Mem T j
          (List_cons T x (hard_seq_to_imported_list xs'))
      with
      | ReflectT H => fun _ => hard_imported_mem_head j x _ H
      | ReflectF _ => fun H => List_Mem_tail T j x _
          (hard_seq_mem_to_imported j xs' H)
      end
  end.

Lemma hard_seq_mem_tail {T : eqType} (j x : T) (xs : seq T) :
  j \in xs -> j \in x :: xs.
Proof. rewrite in_cons. move=> H. apply/orP. right. exact H. Qed.

Fixpoint hard_imported_mem_to_strict_seq {T : eqType} (j : T) (xs : seq T)
    (H : List_Mem T j (hard_seq_to_imported_list xs)) :
    StrictlyInhabited (j \in xs) :=
  match xs as xs0 return
      List_Mem T j (hard_seq_to_imported_list xs0) ->
      StrictlyInhabited (j \in xs0)
  with
  | [::] => fun H0 =>
      match H0 in List_Mem _ _ zs return
        match zs with
        | List_nil => StrictlyInhabited (is_true false)
        | List_cons _ _ => StrictlyInhabited (is_true true)
        end
      with
      | List_Mem_head _ => strictly_inhabits (Logic.eq_refl true)
      | List_Mem_tail _ _ _ => strictly_inhabits (Logic.eq_refl true)
      end
  | x :: xs' => fun H0 =>
      match H0 with
      | List_Mem_head _ =>
          strictly_inhabits (mem_head j xs')
      | List_Mem_tail _ _ Htail =>
          match hard_imported_mem_to_strict_seq j xs' Htail with
          | strictly_inhabits Hmem =>
              strictly_inhabits (hard_seq_mem_tail j x xs' Hmem)
          end
      end
  end H.

Definition original_nin_rem_all_statement (T : eqType) (x : T) (xs : seq T) : Prop :=
  ~ (x \in Generated_util__list.rem_all x xs).

Definition imported_nin_rem_all_statement (T : eqType) (x : T) (xs : seq T) : SProp :=
  Not (Membership_mem T (List T) (List_instMembership T)
    (Prosa_Util_List_rem_all T (hard_decidable_eq T) x
      (hard_seq_to_imported_list xs)) x).

Definition original_nin_rem_all_has_expected_statement
    (T : eqType) (x : T) (xs : seq T) :
    original_nin_rem_all_statement T x xs :=
  @Generated_util__list.nin_rem_all T x xs.

Definition imported_nin_rem_all_has_expected_statement
    (T : eqType) (x : T) (xs : seq T) :
    imported_nin_rem_all_statement T x xs :=
  Prosa_Util_List_nin_rem_all T (hard_decidable_eq T) x
    (hard_seq_to_imported_list xs).

Theorem nin_rem_all_statement_certificate (T : eqType) (x : T) (xs : seq T) :
  PropSPropRel
    (original_nin_rem_all_statement T x xs)
    (imported_nin_rem_all_statement T x xs).
Proof.
  unfold original_nin_rem_all_statement, imported_nin_rem_all_statement.
  apply prop_sprop_rel_intro.
  - intros Hnot Hmem.
    have Hrel := rem_all_recursive_certificate T x xs.
    have Hdecoded := hard_imported_mem_transport x _ _
      (hard_imported_eq_sym _ _ Hrel) Hmem.
    exact (hard_coq_false_to_imported_false
      (Hnot (interpret_strict _
        (hard_imported_mem_to_strict_seq x
          (Generated_util__list.rem_all x xs) Hdecoded))).
  - intro Hnot.
    case E: (x \in Generated_util__list.rem_all x xs).
    + have Hmem0 := hard_seq_mem_to_imported x
        (Generated_util__list.rem_all x xs) hard_sI.
      have Hmem := hard_imported_mem_transport x _ _
        (rem_all_recursive_certificate T x xs) Hmem0.
      exact (match Hnot Hmem return
        StrictlyInhabited (~ (x \in Generated_util__list.rem_all x xs))
      with end).
    + apply strictly_inhabits. intro Htrue.
      rewrite E in Htrue. discriminate Htrue.
Qed.
*)

Print Assumptions spin_idle_constructor_certificate.
Print Assumptions spin_spin_constructor_certificate.
Print Assumptions spin_progress_constructor_certificate.
Print Assumptions spin_scheduled_on_certificate.
Print Assumptions rem_all_recursive_certificate.
