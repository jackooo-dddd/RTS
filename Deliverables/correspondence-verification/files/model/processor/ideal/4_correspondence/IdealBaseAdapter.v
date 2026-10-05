From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdeal.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive IdealFalse : SProp := .
Inductive IdealTrue : SProp := ideal_true_intro.

Definition ideal_false_elim (Q : SProp) (H : IdealFalse) : Q :=
  match H return Q with end.

Definition ideal_false_to_strict (H : IdealFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition ideal_coq_false_to_target (H : Logic.False) :
    ImportedIdeal.False := match H return ImportedIdeal.False with end.

Definition ideal_bool_to_imported (b : bool) : ImportedIdeal.Bool :=
  match b with
  | true => ImportedIdeal.Bool_true
  | false => ImportedIdeal.Bool_false
  end.

Definition ideal_bool_to_rocq (b : ImportedIdeal.Bool) : bool :=
  match b with
  | ImportedIdeal.Bool_true => true
  | ImportedIdeal.Bool_false => false
  end.

Definition IdealBoolRel (bR : bool) (bL : ImportedIdeal.Bool) : SProp :=
  Lean.eq (ideal_bool_to_imported bR) bL.

Lemma ideal_bool_source_roundtrip (b : bool) :
  Logic.eq (ideal_bool_to_rocq (ideal_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ideal_bool_target_roundtrip (b : ImportedIdeal.Bool) :
  Lean.eq (ideal_bool_to_imported (ideal_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition ideal_false_ne_true
    (H : Lean.eq ImportedIdeal.Bool_false ImportedIdeal.Bool_true) :
    IdealFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedIdeal.Bool_false => IdealTrue
    | ImportedIdeal.Bool_true => IdealFalse
    end
  with
  | Lean.eq_refl => ideal_true_intro
  end.

Lemma ideal_bool_truth_correspondence bR bL :
  IdealBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedIdeal.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (ideal_false_to_strict (ideal_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition ideal_decidable_eq (T : eqType) : ImportedIdeal.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedIdeal.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedIdeal.Decidable_isFalse (Lean.eq x y)
        (fun HL => ideal_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint ideal_list_to_imported {T : Type} (xs : seq T) :
    ImportedIdeal.List T :=
  match xs with
  | [::] => ImportedIdeal.List_nil T
  | x :: tail => ImportedIdeal.List_cons T x
      (ideal_list_to_imported tail)
  end.

Fixpoint ideal_list_to_rocq {T : Type} (xs : ImportedIdeal.List T) :
    seq T :=
  match xs with
  | ImportedIdeal.List_nil => [::]
  | ImportedIdeal.List_cons x tail => x :: ideal_list_to_rocq tail
  end.

Definition IdealListRel {T : Type} (xsR : seq T)
    (xsL : ImportedIdeal.List T) : SProp :=
  Lean.eq (ideal_list_to_imported xsR) xsL.

Lemma ideal_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (ideal_list_to_rocq (ideal_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma ideal_list_target_roundtrip {T : Type}
    (xs : ImportedIdeal.List T) :
  Lean.eq (ideal_list_to_imported (ideal_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedIdeal.List_cons T x) _ _ IH).
Qed.

Definition ideal_target_mem {T : Type} (x : T)
    (xs : ImportedIdeal.List T) : SProp :=
  ImportedIdeal.Membership_mem T (ImportedIdeal.List T)
    (ImportedIdeal.List_instMembership T) xs x.

Definition ideal_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedIdeal.List T) :
  Lean.eq xs ys -> ImportedIdeal.List_Mem T x xs ->
  ImportedIdeal.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedIdeal.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition ideal_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedIdeal.List T) : Logic.eq x y ->
    ImportedIdeal.List_Mem T x (ImportedIdeal.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedIdeal.List_Mem T x (ImportedIdeal.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedIdeal.List_Mem_head T x xs
    end.

Definition ideal_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition ideal_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition ideal_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint ideal_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedIdeal.List_Mem T x (ideal_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedIdeal.List_Mem T x (ideal_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedIdeal.List_Mem T x
          (ImportedIdeal.List_cons T y (ideal_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => ideal_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedIdeal.List_Mem_tail T x y _
          (ideal_seq_mem_forward x ys H)
      end
  end.

Fixpoint ideal_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedIdeal.List T)
    (H : ImportedIdeal.List_Mem T x xs) :
    SubNatTruth (x \in ideal_list_to_rocq xs) :=
  match H with
  | ImportedIdeal.List_Mem_head ys =>
      ideal_mem_head_truth _ _ (ideal_eq_refl_truth T x)
  | ImportedIdeal.List_Mem_tail y ys Htail =>
      ideal_mem_tail_truth _ _
        (ideal_imported_mem_decoded x ys Htail)
  end.

Definition ideal_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma ideal_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedIdeal.List T) :
  IdealListRel xsR xsL ->
  PropSPropRel (x \in xsR) (ideal_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold ideal_target_mem.
    apply (ideal_list_mem_transport x _ _ Hxs).
    apply ideal_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (ideal_mem_truth_transport x _ _
      (ideal_list_source_roundtrip xsR)).
    apply ideal_imported_mem_decoded.
    unfold ideal_target_mem in Hmem.
    exact (ideal_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ideal_bool_source_roundtrip". exact I.
Qed.
Print Assumptions ideal_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ideal_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ideal_bool_target_roundtrip". exact I.
Qed.
Print Assumptions ideal_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ideal_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ideal_bool_truth_correspondence". exact I.
Qed.
Print Assumptions ideal_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ideal_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ideal_list_source_roundtrip". exact I.
Qed.
Print Assumptions ideal_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ideal_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ideal_list_target_roundtrip". exact I.
Qed.
Print Assumptions ideal_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ideal_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ideal_membership_correspondence". exact I.
Qed.
Print Assumptions ideal_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ideal_membership_correspondence". exact I.
Qed.
