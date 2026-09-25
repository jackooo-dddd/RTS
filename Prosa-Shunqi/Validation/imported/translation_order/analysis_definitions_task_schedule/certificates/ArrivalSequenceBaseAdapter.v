From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskSchedule.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive ArFalse : SProp := .
Inductive ArTrue : SProp := ar_true_intro.

Definition ar_false_elim (Q : SProp) (H : ArFalse) : Q :=
  match H return Q with end.

Definition ar_false_to_strict (H : ArFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition ar_coq_false_to_target (H : Logic.False) :
    ImportedTaskSchedule.False := match H return ImportedTaskSchedule.False with end.

Definition ar_bool_to_imported (b : bool) : ImportedTaskSchedule.Bool :=
  match b with
  | true => ImportedTaskSchedule.Bool_true
  | false => ImportedTaskSchedule.Bool_false
  end.

Definition ar_bool_to_rocq (b : ImportedTaskSchedule.Bool) : bool :=
  match b with
  | ImportedTaskSchedule.Bool_true => true
  | ImportedTaskSchedule.Bool_false => false
  end.

Definition ArBoolRel (bR : bool) (bL : ImportedTaskSchedule.Bool) : SProp :=
  Lean.eq (ar_bool_to_imported bR) bL.

Lemma ar_bool_source_roundtrip (b : bool) :
  Logic.eq (ar_bool_to_rocq (ar_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ar_bool_target_roundtrip (b : ImportedTaskSchedule.Bool) :
  Lean.eq (ar_bool_to_imported (ar_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition ar_false_ne_true
    (H : Lean.eq ImportedTaskSchedule.Bool_false ImportedTaskSchedule.Bool_true) :
    ArFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedTaskSchedule.Bool_false => ArTrue
    | ImportedTaskSchedule.Bool_true => ArFalse
    end
  with
  | Lean.eq_refl => ar_true_intro
  end.

Lemma ar_bool_truth_correspondence bR bL :
  ArBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedTaskSchedule.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (ar_false_to_strict (ar_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition ar_decidable_eq (T : eqType) : ImportedTaskSchedule.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedTaskSchedule.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedTaskSchedule.Decidable_isFalse (Lean.eq x y)
        (fun HL => ar_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint ar_list_to_imported {T : Type} (xs : seq T) :
    ImportedTaskSchedule.List T :=
  match xs with
  | [::] => ImportedTaskSchedule.List_nil T
  | x :: tail => ImportedTaskSchedule.List_cons T x
      (ar_list_to_imported tail)
  end.

Fixpoint ar_list_to_rocq {T : Type} (xs : ImportedTaskSchedule.List T) :
    seq T :=
  match xs with
  | ImportedTaskSchedule.List_nil => [::]
  | ImportedTaskSchedule.List_cons x tail => x :: ar_list_to_rocq tail
  end.

Definition ArListRel {T : Type} (xsR : seq T)
    (xsL : ImportedTaskSchedule.List T) : SProp :=
  Lean.eq (ar_list_to_imported xsR) xsL.

Lemma ar_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (ar_list_to_rocq (ar_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma ar_list_target_roundtrip {T : Type}
    (xs : ImportedTaskSchedule.List T) :
  Lean.eq (ar_list_to_imported (ar_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedTaskSchedule.List_cons T x) _ _ IH).
Qed.

Definition ar_target_mem {T : Type} (x : T)
    (xs : ImportedTaskSchedule.List T) : SProp :=
  ImportedTaskSchedule.Membership_mem T (ImportedTaskSchedule.List T)
    (ImportedTaskSchedule.List_instMembership T) xs x.

Definition ar_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedTaskSchedule.List T) :
  Lean.eq xs ys -> ImportedTaskSchedule.List_Mem T x xs ->
  ImportedTaskSchedule.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedTaskSchedule.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition ar_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedTaskSchedule.List T) : Logic.eq x y ->
    ImportedTaskSchedule.List_Mem T x (ImportedTaskSchedule.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedTaskSchedule.List_Mem T x (ImportedTaskSchedule.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedTaskSchedule.List_Mem_head T x xs
    end.

Definition ar_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition ar_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition ar_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint ar_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedTaskSchedule.List_Mem T x (ar_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedTaskSchedule.List_Mem T x (ar_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedTaskSchedule.List_Mem T x
          (ImportedTaskSchedule.List_cons T y (ar_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => ar_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedTaskSchedule.List_Mem_tail T x y _
          (ar_seq_mem_forward x ys H)
      end
  end.

Fixpoint ar_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedTaskSchedule.List T)
    (H : ImportedTaskSchedule.List_Mem T x xs) :
    SubNatTruth (x \in ar_list_to_rocq xs) :=
  match H with
  | ImportedTaskSchedule.List_Mem_head ys =>
      ar_mem_head_truth _ _ (ar_eq_refl_truth T x)
  | ImportedTaskSchedule.List_Mem_tail y ys Htail =>
      ar_mem_tail_truth _ _
        (ar_imported_mem_decoded x ys Htail)
  end.

Definition ar_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma ar_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedTaskSchedule.List T) :
  ArListRel xsR xsL ->
  PropSPropRel (x \in xsR) (ar_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold ar_target_mem.
    apply (ar_list_mem_transport x _ _ Hxs).
    apply ar_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (ar_mem_truth_transport x _ _
      (ar_list_source_roundtrip xsR)).
    apply ar_imported_mem_decoded.
    unfold ar_target_mem in Hmem.
    exact (ar_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_bool_source_roundtrip". exact I.
Qed.
Print Assumptions ar_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_bool_target_roundtrip". exact I.
Qed.
Print Assumptions ar_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_bool_truth_correspondence". exact I.
Qed.
Print Assumptions ar_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_list_source_roundtrip". exact I.
Qed.
Print Assumptions ar_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_list_target_roundtrip". exact I.
Qed.
Print Assumptions ar_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_membership_correspondence". exact I.
Qed.
Print Assumptions ar_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_membership_correspondence". exact I.
Qed.
