(** Artifact-local instantiation of the accepted Bool/List adapter template:
    IdealUniExceedFactsBaseAdapter.v, SHA-256
    93b82dfed76a98760b1fae5c9f73953f251141ee7350ac256f3360289f76bb7a.
    This instance is kernel-checked against ImportedTaskCost. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskCost.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive TcFalse : SProp := .
Inductive TcTrue : SProp := tc_true_intro.

Definition tc_false_elim (Q : SProp) (H : TcFalse) : Q :=
  match H return Q with end.

Definition tc_false_to_strict (H : TcFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition tc_coq_false_to_target (H : Logic.False) :
    ImportedTaskCost.False := match H return ImportedTaskCost.False with end.

Definition tc_bool_to_imported (b : bool) : ImportedTaskCost.Bool :=
  match b with
  | true => ImportedTaskCost.Bool_true
  | false => ImportedTaskCost.Bool_false
  end.

Definition tc_bool_to_rocq (b : ImportedTaskCost.Bool) : bool :=
  match b with
  | ImportedTaskCost.Bool_true => true
  | ImportedTaskCost.Bool_false => false
  end.

Definition TcBoolRel (bR : bool) (bL : ImportedTaskCost.Bool) : SProp :=
  Lean.eq (tc_bool_to_imported bR) bL.

Lemma tc_bool_source_roundtrip (b : bool) :
  Logic.eq (tc_bool_to_rocq (tc_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma tc_bool_target_roundtrip (b : ImportedTaskCost.Bool) :
  Lean.eq (tc_bool_to_imported (tc_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition tc_false_ne_true
    (H : Lean.eq ImportedTaskCost.Bool_false ImportedTaskCost.Bool_true) :
    TcFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedTaskCost.Bool_false => TcTrue
    | ImportedTaskCost.Bool_true => TcFalse
    end
  with
  | Lean.eq_refl => tc_true_intro
  end.

Lemma tc_bool_truth_correspondence bR bL :
  TcBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedTaskCost.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (tc_false_to_strict (tc_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition tc_decidable_eq (T : eqType) : ImportedTaskCost.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedTaskCost.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedTaskCost.Decidable_isFalse (Lean.eq x y)
        (fun HL => tc_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint tc_list_to_imported {T : Type} (xs : seq T) :
    ImportedTaskCost.List T :=
  match xs with
  | [::] => ImportedTaskCost.List_nil T
  | x :: tail => ImportedTaskCost.List_cons T x
      (tc_list_to_imported tail)
  end.

Fixpoint tc_list_to_rocq {T : Type} (xs : ImportedTaskCost.List T) :
    seq T :=
  match xs with
  | ImportedTaskCost.List_nil => [::]
  | ImportedTaskCost.List_cons x tail => x :: tc_list_to_rocq tail
  end.

Definition TcListRel {T : Type} (xsR : seq T)
    (xsL : ImportedTaskCost.List T) : SProp :=
  Lean.eq (tc_list_to_imported xsR) xsL.

Lemma tc_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (tc_list_to_rocq (tc_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma tc_list_target_roundtrip {T : Type}
    (xs : ImportedTaskCost.List T) :
  Lean.eq (tc_list_to_imported (tc_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedTaskCost.List_cons T x) _ _ IH).
Qed.

Definition tc_target_mem {T : Type} (x : T)
    (xs : ImportedTaskCost.List T) : SProp :=
  ImportedTaskCost.Membership_mem T (ImportedTaskCost.List T)
    (ImportedTaskCost.List_instMembership T) xs x.

Definition tc_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedTaskCost.List T) :
  Lean.eq xs ys -> ImportedTaskCost.List_Mem T x xs ->
  ImportedTaskCost.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedTaskCost.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition tc_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedTaskCost.List T) : Logic.eq x y ->
    ImportedTaskCost.List_Mem T x (ImportedTaskCost.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedTaskCost.List_Mem T x (ImportedTaskCost.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedTaskCost.List_Mem_head T x xs
    end.

Definition tc_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition tc_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition tc_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint tc_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedTaskCost.List_Mem T x (tc_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedTaskCost.List_Mem T x (tc_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedTaskCost.List_Mem T x
          (ImportedTaskCost.List_cons T y (tc_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => tc_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedTaskCost.List_Mem_tail T x y _
          (tc_seq_mem_forward x ys H)
      end
  end.

Fixpoint tc_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedTaskCost.List T)
    (H : ImportedTaskCost.List_Mem T x xs) :
    SubNatTruth (x \in tc_list_to_rocq xs) :=
  match H with
  | ImportedTaskCost.List_Mem_head ys =>
      tc_mem_head_truth _ _ (tc_eq_refl_truth T x)
  | ImportedTaskCost.List_Mem_tail y ys Htail =>
      tc_mem_tail_truth _ _
        (tc_imported_mem_decoded x ys Htail)
  end.

Definition tc_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma tc_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedTaskCost.List T) :
  TcListRel xsR xsL ->
  PropSPropRel (x \in xsR) (tc_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold tc_target_mem.
    apply (tc_list_mem_transport x _ _ Hxs).
    apply tc_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (tc_mem_truth_transport x _ _
      (tc_list_source_roundtrip xsR)).
    apply tc_imported_mem_decoded.
    unfold tc_target_mem in Hmem.
    exact (tc_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN tc_bool_source_roundtrip". exact I.
Qed.
Print Assumptions tc_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END tc_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN tc_bool_target_roundtrip". exact I.
Qed.
Print Assumptions tc_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END tc_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN tc_bool_truth_correspondence". exact I.
Qed.
Print Assumptions tc_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END tc_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN tc_list_source_roundtrip". exact I.
Qed.
Print Assumptions tc_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END tc_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN tc_list_target_roundtrip". exact I.
Qed.
Print Assumptions tc_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END tc_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN tc_membership_correspondence". exact I.
Qed.
Print Assumptions tc_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END tc_membership_correspondence". exact I.
Qed.
