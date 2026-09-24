From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheads.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive OvhFalse : SProp := .
Inductive OvhTrue : SProp := ovh_true_intro.

Definition ovh_false_elim (Q : SProp) (H : OvhFalse) : Q :=
  match H return Q with end.

Definition ovh_false_to_strict (H : OvhFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition ovh_coq_false_to_target (H : Logic.False) :
    ImportedOverheads.False := match H return ImportedOverheads.False with end.

Definition ovh_bool_to_imported (b : bool) : ImportedOverheads.Bool :=
  match b with
  | true => ImportedOverheads.Bool_true
  | false => ImportedOverheads.Bool_false
  end.

Definition ovh_bool_to_rocq (b : ImportedOverheads.Bool) : bool :=
  match b with
  | ImportedOverheads.Bool_true => true
  | ImportedOverheads.Bool_false => false
  end.

Definition OvhBoolRel (bR : bool) (bL : ImportedOverheads.Bool) : SProp :=
  Lean.eq (ovh_bool_to_imported bR) bL.

Lemma ovh_bool_source_roundtrip (b : bool) :
  Logic.eq (ovh_bool_to_rocq (ovh_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ovh_bool_target_roundtrip (b : ImportedOverheads.Bool) :
  Lean.eq (ovh_bool_to_imported (ovh_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition ovh_false_ne_true
    (H : Lean.eq ImportedOverheads.Bool_false ImportedOverheads.Bool_true) :
    OvhFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedOverheads.Bool_false => OvhTrue
    | ImportedOverheads.Bool_true => OvhFalse
    end
  with
  | Lean.eq_refl => ovh_true_intro
  end.

Lemma ovh_bool_truth_correspondence bR bL :
  OvhBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedOverheads.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (ovh_false_to_strict (ovh_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition ovh_decidable_eq (T : eqType) : ImportedOverheads.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedOverheads.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedOverheads.Decidable_isFalse (Lean.eq x y)
        (fun HL => ovh_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint ovh_list_to_imported {T : Type} (xs : seq T) :
    ImportedOverheads.List T :=
  match xs with
  | [::] => ImportedOverheads.List_nil T
  | x :: tail => ImportedOverheads.List_cons T x
      (ovh_list_to_imported tail)
  end.

Fixpoint ovh_list_to_rocq {T : Type} (xs : ImportedOverheads.List T) :
    seq T :=
  match xs with
  | ImportedOverheads.List_nil => [::]
  | ImportedOverheads.List_cons x tail => x :: ovh_list_to_rocq tail
  end.

Definition OvhListRel {T : Type} (xsR : seq T)
    (xsL : ImportedOverheads.List T) : SProp :=
  Lean.eq (ovh_list_to_imported xsR) xsL.

Lemma ovh_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (ovh_list_to_rocq (ovh_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma ovh_list_target_roundtrip {T : Type}
    (xs : ImportedOverheads.List T) :
  Lean.eq (ovh_list_to_imported (ovh_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedOverheads.List_cons T x) _ _ IH).
Qed.

Definition ovh_target_mem {T : Type} (x : T)
    (xs : ImportedOverheads.List T) : SProp :=
  ImportedOverheads.Membership_mem T (ImportedOverheads.List T)
    (ImportedOverheads.List_instMembership T) xs x.

Definition ovh_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedOverheads.List T) :
  Lean.eq xs ys -> ImportedOverheads.List_Mem T x xs ->
  ImportedOverheads.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedOverheads.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition ovh_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedOverheads.List T) : Logic.eq x y ->
    ImportedOverheads.List_Mem T x (ImportedOverheads.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedOverheads.List_Mem T x (ImportedOverheads.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedOverheads.List_Mem_head T x xs
    end.

Definition ovh_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition ovh_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition ovh_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint ovh_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedOverheads.List_Mem T x (ovh_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedOverheads.List_Mem T x (ovh_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedOverheads.List_Mem T x
          (ImportedOverheads.List_cons T y (ovh_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => ovh_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedOverheads.List_Mem_tail T x y _
          (ovh_seq_mem_forward x ys H)
      end
  end.

Fixpoint ovh_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedOverheads.List T)
    (H : ImportedOverheads.List_Mem T x xs) :
    SubNatTruth (x \in ovh_list_to_rocq xs) :=
  match H with
  | ImportedOverheads.List_Mem_head ys =>
      ovh_mem_head_truth _ _ (ovh_eq_refl_truth T x)
  | ImportedOverheads.List_Mem_tail y ys Htail =>
      ovh_mem_tail_truth _ _
        (ovh_imported_mem_decoded x ys Htail)
  end.

Definition ovh_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma ovh_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedOverheads.List T) :
  OvhListRel xsR xsL ->
  PropSPropRel (x \in xsR) (ovh_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold ovh_target_mem.
    apply (ovh_list_mem_transport x _ _ Hxs).
    apply ovh_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (ovh_mem_truth_transport x _ _
      (ovh_list_source_roundtrip xsR)).
    apply ovh_imported_mem_decoded.
    unfold ovh_target_mem in Hmem.
    exact (ovh_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ovh_bool_source_roundtrip". exact I.
Qed.
Print Assumptions ovh_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ovh_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ovh_bool_target_roundtrip". exact I.
Qed.
Print Assumptions ovh_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ovh_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ovh_bool_truth_correspondence". exact I.
Qed.
Print Assumptions ovh_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ovh_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ovh_list_source_roundtrip". exact I.
Qed.
Print Assumptions ovh_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ovh_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ovh_list_target_roundtrip". exact I.
Qed.
Print Assumptions ovh_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ovh_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ovh_membership_correspondence". exact I.
Qed.
Print Assumptions ovh_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ovh_membership_correspondence". exact I.
Qed.
