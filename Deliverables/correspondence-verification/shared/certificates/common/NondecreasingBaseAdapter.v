From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedNondecreasing.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive NdFalse : SProp := .
Inductive NdTrue : SProp := nd_true_intro.

Definition nd_false_elim (Q : SProp) (H : NdFalse) : Q :=
  match H return Q with end.

Definition nd_false_to_strict (H : NdFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition nd_coq_false_to_target (H : Logic.False) :
    ImportedNondecreasing.False := match H return ImportedNondecreasing.False with end.

Definition nd_bool_to_imported (b : bool) : ImportedNondecreasing.Bool :=
  match b with
  | true => ImportedNondecreasing.Bool_true
  | false => ImportedNondecreasing.Bool_false
  end.

Definition nd_bool_to_rocq (b : ImportedNondecreasing.Bool) : bool :=
  match b with
  | ImportedNondecreasing.Bool_true => true
  | ImportedNondecreasing.Bool_false => false
  end.

Definition NdBoolRel (bR : bool) (bL : ImportedNondecreasing.Bool) : SProp :=
  Lean.eq (nd_bool_to_imported bR) bL.

Lemma nd_bool_source_roundtrip (b : bool) :
  Logic.eq (nd_bool_to_rocq (nd_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma nd_bool_target_roundtrip (b : ImportedNondecreasing.Bool) :
  Lean.eq (nd_bool_to_imported (nd_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition nd_false_ne_true
    (H : Lean.eq ImportedNondecreasing.Bool_false ImportedNondecreasing.Bool_true) :
    NdFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedNondecreasing.Bool_false => NdTrue
    | ImportedNondecreasing.Bool_true => NdFalse
    end
  with
  | Lean.eq_refl => nd_true_intro
  end.

Lemma nd_bool_truth_correspondence bR bL :
  NdBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedNondecreasing.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (nd_false_to_strict (nd_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition nd_decidable_eq (T : eqType) : ImportedNondecreasing.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedNondecreasing.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedNondecreasing.Decidable_isFalse (Lean.eq x y)
        (fun HL => nd_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint nd_list_to_imported {T : Type} (xs : seq T) :
    ImportedNondecreasing.List T :=
  match xs with
  | [::] => ImportedNondecreasing.List_nil T
  | x :: tail => ImportedNondecreasing.List_cons T x
      (nd_list_to_imported tail)
  end.

Fixpoint nd_list_to_rocq {T : Type} (xs : ImportedNondecreasing.List T) :
    seq T :=
  match xs with
  | ImportedNondecreasing.List_nil => [::]
  | ImportedNondecreasing.List_cons x tail => x :: nd_list_to_rocq tail
  end.

Definition NdListRel {T : Type} (xsR : seq T)
    (xsL : ImportedNondecreasing.List T) : SProp :=
  Lean.eq (nd_list_to_imported xsR) xsL.

Lemma nd_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (nd_list_to_rocq (nd_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma nd_list_target_roundtrip {T : Type}
    (xs : ImportedNondecreasing.List T) :
  Lean.eq (nd_list_to_imported (nd_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedNondecreasing.List_cons T x) _ _ IH).
Qed.

Definition nd_target_mem {T : Type} (x : T)
    (xs : ImportedNondecreasing.List T) : SProp :=
  ImportedNondecreasing.Membership_mem T (ImportedNondecreasing.List T)
    (ImportedNondecreasing.List_instMembership T) xs x.

Definition nd_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedNondecreasing.List T) :
  Lean.eq xs ys -> ImportedNondecreasing.List_Mem T x xs ->
  ImportedNondecreasing.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedNondecreasing.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition nd_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedNondecreasing.List T) : Logic.eq x y ->
    ImportedNondecreasing.List_Mem T x (ImportedNondecreasing.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedNondecreasing.List_Mem T x (ImportedNondecreasing.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedNondecreasing.List_Mem_head T x xs
    end.

Definition nd_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition nd_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition nd_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint nd_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedNondecreasing.List_Mem T x (nd_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedNondecreasing.List_Mem T x (nd_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedNondecreasing.List_Mem T x
          (ImportedNondecreasing.List_cons T y (nd_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => nd_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedNondecreasing.List_Mem_tail T x y _
          (nd_seq_mem_forward x ys H)
      end
  end.

Fixpoint nd_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedNondecreasing.List T)
    (H : ImportedNondecreasing.List_Mem T x xs) :
    SubNatTruth (x \in nd_list_to_rocq xs) :=
  match H with
  | ImportedNondecreasing.List_Mem_head ys =>
      nd_mem_head_truth _ _ (nd_eq_refl_truth T x)
  | ImportedNondecreasing.List_Mem_tail y ys Htail =>
      nd_mem_tail_truth _ _
        (nd_imported_mem_decoded x ys Htail)
  end.

Definition nd_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma nd_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedNondecreasing.List T) :
  NdListRel xsR xsL ->
  PropSPropRel (x \in xsR) (nd_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold nd_target_mem.
    apply (nd_list_mem_transport x _ _ Hxs).
    apply nd_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (nd_mem_truth_transport x _ _
      (nd_list_source_roundtrip xsR)).
    apply nd_imported_mem_decoded.
    unfold nd_target_mem in Hmem.
    exact (nd_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN nd_bool_source_roundtrip". exact I.
Qed.
Print Assumptions nd_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END nd_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN nd_bool_target_roundtrip". exact I.
Qed.
Print Assumptions nd_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END nd_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN nd_bool_truth_correspondence". exact I.
Qed.
Print Assumptions nd_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END nd_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN nd_list_source_roundtrip". exact I.
Qed.
Print Assumptions nd_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END nd_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN nd_list_target_roundtrip". exact I.
Qed.
Print Assumptions nd_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END nd_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN nd_membership_correspondence". exact I.
Qed.
Print Assumptions nd_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END nd_membership_correspondence". exact I.
Qed.
