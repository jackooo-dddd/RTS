From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealUniExceed.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive IueFalse : SProp := .
Inductive IueTrue : SProp := iue_true_intro.

Definition iue_false_elim (Q : SProp) (H : IueFalse) : Q :=
  match H return Q with end.

Definition iue_false_to_strict (H : IueFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition iue_coq_false_to_target (H : Logic.False) :
    ImportedIdealUniExceed.False := match H return ImportedIdealUniExceed.False with end.

Definition iue_bool_to_imported (b : bool) : ImportedIdealUniExceed.Bool :=
  match b with
  | true => ImportedIdealUniExceed.Bool_true
  | false => ImportedIdealUniExceed.Bool_false
  end.

Definition iue_bool_to_rocq (b : ImportedIdealUniExceed.Bool) : bool :=
  match b with
  | ImportedIdealUniExceed.Bool_true => true
  | ImportedIdealUniExceed.Bool_false => false
  end.

Definition IueBoolRel (bR : bool) (bL : ImportedIdealUniExceed.Bool) : SProp :=
  Lean.eq (iue_bool_to_imported bR) bL.

Lemma iue_bool_source_roundtrip (b : bool) :
  Logic.eq (iue_bool_to_rocq (iue_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma iue_bool_target_roundtrip (b : ImportedIdealUniExceed.Bool) :
  Lean.eq (iue_bool_to_imported (iue_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition iue_false_ne_true
    (H : Lean.eq ImportedIdealUniExceed.Bool_false ImportedIdealUniExceed.Bool_true) :
    IueFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedIdealUniExceed.Bool_false => IueTrue
    | ImportedIdealUniExceed.Bool_true => IueFalse
    end
  with
  | Lean.eq_refl => iue_true_intro
  end.

Lemma iue_bool_truth_correspondence bR bL :
  IueBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedIdealUniExceed.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (iue_false_to_strict (iue_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition iue_decidable_eq (T : eqType) : ImportedIdealUniExceed.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedIdealUniExceed.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedIdealUniExceed.Decidable_isFalse (Lean.eq x y)
        (fun HL => iue_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint iue_list_to_imported {T : Type} (xs : seq T) :
    ImportedIdealUniExceed.List T :=
  match xs with
  | [::] => ImportedIdealUniExceed.List_nil T
  | x :: tail => ImportedIdealUniExceed.List_cons T x
      (iue_list_to_imported tail)
  end.

Fixpoint iue_list_to_rocq {T : Type} (xs : ImportedIdealUniExceed.List T) :
    seq T :=
  match xs with
  | ImportedIdealUniExceed.List_nil => [::]
  | ImportedIdealUniExceed.List_cons x tail => x :: iue_list_to_rocq tail
  end.

Definition IueListRel {T : Type} (xsR : seq T)
    (xsL : ImportedIdealUniExceed.List T) : SProp :=
  Lean.eq (iue_list_to_imported xsR) xsL.

Lemma iue_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (iue_list_to_rocq (iue_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma iue_list_target_roundtrip {T : Type}
    (xs : ImportedIdealUniExceed.List T) :
  Lean.eq (iue_list_to_imported (iue_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedIdealUniExceed.List_cons T x) _ _ IH).
Qed.

Definition iue_target_mem {T : Type} (x : T)
    (xs : ImportedIdealUniExceed.List T) : SProp :=
  ImportedIdealUniExceed.Membership_mem T (ImportedIdealUniExceed.List T)
    (ImportedIdealUniExceed.List_instMembership T) xs x.

Definition iue_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedIdealUniExceed.List T) :
  Lean.eq xs ys -> ImportedIdealUniExceed.List_Mem T x xs ->
  ImportedIdealUniExceed.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedIdealUniExceed.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition iue_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedIdealUniExceed.List T) : Logic.eq x y ->
    ImportedIdealUniExceed.List_Mem T x (ImportedIdealUniExceed.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedIdealUniExceed.List_Mem T x (ImportedIdealUniExceed.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedIdealUniExceed.List_Mem_head T x xs
    end.

Definition iue_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition iue_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition iue_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint iue_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedIdealUniExceed.List_Mem T x (iue_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedIdealUniExceed.List_Mem T x (iue_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedIdealUniExceed.List_Mem T x
          (ImportedIdealUniExceed.List_cons T y (iue_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => iue_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedIdealUniExceed.List_Mem_tail T x y _
          (iue_seq_mem_forward x ys H)
      end
  end.

Fixpoint iue_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedIdealUniExceed.List T)
    (H : ImportedIdealUniExceed.List_Mem T x xs) :
    SubNatTruth (x \in iue_list_to_rocq xs) :=
  match H with
  | ImportedIdealUniExceed.List_Mem_head ys =>
      iue_mem_head_truth _ _ (iue_eq_refl_truth T x)
  | ImportedIdealUniExceed.List_Mem_tail y ys Htail =>
      iue_mem_tail_truth _ _
        (iue_imported_mem_decoded x ys Htail)
  end.

Definition iue_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma iue_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedIdealUniExceed.List T) :
  IueListRel xsR xsL ->
  PropSPropRel (x \in xsR) (iue_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold iue_target_mem.
    apply (iue_list_mem_transport x _ _ Hxs).
    apply iue_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (iue_mem_truth_transport x _ _
      (iue_list_source_roundtrip xsR)).
    apply iue_imported_mem_decoded.
    unfold iue_target_mem in Hmem.
    exact (iue_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN iue_bool_source_roundtrip". exact I.
Qed.
Print Assumptions iue_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END iue_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN iue_bool_target_roundtrip". exact I.
Qed.
Print Assumptions iue_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END iue_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN iue_bool_truth_correspondence". exact I.
Qed.
Print Assumptions iue_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END iue_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN iue_list_source_roundtrip". exact I.
Qed.
Print Assumptions iue_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END iue_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN iue_list_target_roundtrip". exact I.
Qed.
Print Assumptions iue_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END iue_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN iue_membership_correspondence". exact I.
Qed.
Print Assumptions iue_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END iue_membership_correspondence". exact I.
Qed.
