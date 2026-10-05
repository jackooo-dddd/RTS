From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJobProperties.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive JpFalse : SProp := .
Inductive JpTrue : SProp := jp_true_intro.

Definition jp_false_elim (Q : SProp) (H : JpFalse) : Q :=
  match H return Q with end.

Definition jp_false_to_strict (H : JpFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition jp_coq_false_to_target (H : Logic.False) :
    ImportedJobProperties.False := match H return ImportedJobProperties.False with end.

Definition jp_bool_to_imported (b : bool) : ImportedJobProperties.Bool :=
  match b with
  | true => ImportedJobProperties.Bool_true
  | false => ImportedJobProperties.Bool_false
  end.

Definition jp_bool_to_rocq (b : ImportedJobProperties.Bool) : bool :=
  match b with
  | ImportedJobProperties.Bool_true => true
  | ImportedJobProperties.Bool_false => false
  end.

Definition JpBoolRel (bR : bool) (bL : ImportedJobProperties.Bool) : SProp :=
  Lean.eq (jp_bool_to_imported bR) bL.

Lemma jp_bool_source_roundtrip (b : bool) :
  Logic.eq (jp_bool_to_rocq (jp_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma jp_bool_target_roundtrip (b : ImportedJobProperties.Bool) :
  Lean.eq (jp_bool_to_imported (jp_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition jp_false_ne_true
    (H : Lean.eq ImportedJobProperties.Bool_false ImportedJobProperties.Bool_true) :
    JpFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedJobProperties.Bool_false => JpTrue
    | ImportedJobProperties.Bool_true => JpFalse
    end
  with
  | Lean.eq_refl => jp_true_intro
  end.

Lemma jp_bool_truth_correspondence bR bL :
  JpBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedJobProperties.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (jp_false_to_strict (jp_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition jp_decidable_eq (T : eqType) : ImportedJobProperties.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedJobProperties.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedJobProperties.Decidable_isFalse (Lean.eq x y)
        (fun HL => jp_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint jp_list_to_imported {T : Type} (xs : seq T) :
    ImportedJobProperties.List T :=
  match xs with
  | [::] => ImportedJobProperties.List_nil T
  | x :: tail => ImportedJobProperties.List_cons T x
      (jp_list_to_imported tail)
  end.

Fixpoint jp_list_to_rocq {T : Type} (xs : ImportedJobProperties.List T) :
    seq T :=
  match xs with
  | ImportedJobProperties.List_nil => [::]
  | ImportedJobProperties.List_cons x tail => x :: jp_list_to_rocq tail
  end.

Definition JpListRel {T : Type} (xsR : seq T)
    (xsL : ImportedJobProperties.List T) : SProp :=
  Lean.eq (jp_list_to_imported xsR) xsL.

Lemma jp_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (jp_list_to_rocq (jp_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma jp_list_target_roundtrip {T : Type}
    (xs : ImportedJobProperties.List T) :
  Lean.eq (jp_list_to_imported (jp_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedJobProperties.List_cons T x) _ _ IH).
Qed.

Definition jp_target_mem {T : Type} (x : T)
    (xs : ImportedJobProperties.List T) : SProp :=
  ImportedJobProperties.Membership_mem T (ImportedJobProperties.List T)
    (ImportedJobProperties.List_instMembership T) xs x.

Definition jp_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedJobProperties.List T) :
  Lean.eq xs ys -> ImportedJobProperties.List_Mem T x xs ->
  ImportedJobProperties.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedJobProperties.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition jp_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedJobProperties.List T) : Logic.eq x y ->
    ImportedJobProperties.List_Mem T x (ImportedJobProperties.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedJobProperties.List_Mem T x (ImportedJobProperties.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedJobProperties.List_Mem_head T x xs
    end.

Definition jp_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition jp_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition jp_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint jp_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedJobProperties.List_Mem T x (jp_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedJobProperties.List_Mem T x (jp_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedJobProperties.List_Mem T x
          (ImportedJobProperties.List_cons T y (jp_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => jp_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedJobProperties.List_Mem_tail T x y _
          (jp_seq_mem_forward x ys H)
      end
  end.

Fixpoint jp_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedJobProperties.List T)
    (H : ImportedJobProperties.List_Mem T x xs) :
    SubNatTruth (x \in jp_list_to_rocq xs) :=
  match H with
  | ImportedJobProperties.List_Mem_head ys =>
      jp_mem_head_truth _ _ (jp_eq_refl_truth T x)
  | ImportedJobProperties.List_Mem_tail y ys Htail =>
      jp_mem_tail_truth _ _
        (jp_imported_mem_decoded x ys Htail)
  end.

Definition jp_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma jp_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedJobProperties.List T) :
  JpListRel xsR xsL ->
  PropSPropRel (x \in xsR) (jp_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold jp_target_mem.
    apply (jp_list_mem_transport x _ _ Hxs).
    apply jp_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (jp_mem_truth_transport x _ _
      (jp_list_source_roundtrip xsR)).
    apply jp_imported_mem_decoded.
    unfold jp_target_mem in Hmem.
    exact (jp_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN jp_bool_source_roundtrip". exact I.
Qed.
Print Assumptions jp_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END jp_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN jp_bool_target_roundtrip". exact I.
Qed.
Print Assumptions jp_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END jp_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN jp_bool_truth_correspondence". exact I.
Qed.
Print Assumptions jp_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END jp_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN jp_list_source_roundtrip". exact I.
Qed.
Print Assumptions jp_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END jp_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN jp_list_target_roundtrip". exact I.
Qed.
Print Assumptions jp_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END jp_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN jp_membership_correspondence". exact I.
Qed.
Print Assumptions jp_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END jp_membership_correspondence". exact I.
Qed.
