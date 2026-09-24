From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRestrictedSupplyFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive RsFalse : SProp := .
Inductive RsTrue : SProp := rs_true_intro.

Definition rs_false_elim (Q : SProp) (H : RsFalse) : Q :=
  match H return Q with end.

Definition rs_false_to_strict (H : RsFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition rs_coq_false_to_target (H : Logic.False) :
    ImportedRestrictedSupplyFull.False := match H return ImportedRestrictedSupplyFull.False with end.

Definition rs_bool_to_imported (b : bool) : ImportedRestrictedSupplyFull.Bool :=
  match b with
  | true => ImportedRestrictedSupplyFull.Bool_true
  | false => ImportedRestrictedSupplyFull.Bool_false
  end.

Definition rs_bool_to_rocq (b : ImportedRestrictedSupplyFull.Bool) : bool :=
  match b with
  | ImportedRestrictedSupplyFull.Bool_true => true
  | ImportedRestrictedSupplyFull.Bool_false => false
  end.

Definition RsBoolRel (bR : bool) (bL : ImportedRestrictedSupplyFull.Bool) : SProp :=
  Lean.eq (rs_bool_to_imported bR) bL.

Lemma rs_bool_source_roundtrip (b : bool) :
  Logic.eq (rs_bool_to_rocq (rs_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma rs_bool_target_roundtrip (b : ImportedRestrictedSupplyFull.Bool) :
  Lean.eq (rs_bool_to_imported (rs_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition rs_false_ne_true
    (H : Lean.eq ImportedRestrictedSupplyFull.Bool_false ImportedRestrictedSupplyFull.Bool_true) :
    RsFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedRestrictedSupplyFull.Bool_false => RsTrue
    | ImportedRestrictedSupplyFull.Bool_true => RsFalse
    end
  with
  | Lean.eq_refl => rs_true_intro
  end.

Lemma rs_bool_truth_correspondence bR bL :
  RsBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedRestrictedSupplyFull.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (rs_false_to_strict (rs_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition rs_decidable_eq (T : eqType) : ImportedRestrictedSupplyFull.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedRestrictedSupplyFull.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedRestrictedSupplyFull.Decidable_isFalse (Lean.eq x y)
        (fun HL => rs_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint rs_list_to_imported {T : Type} (xs : seq T) :
    ImportedRestrictedSupplyFull.List T :=
  match xs with
  | [::] => ImportedRestrictedSupplyFull.List_nil T
  | x :: tail => ImportedRestrictedSupplyFull.List_cons T x
      (rs_list_to_imported tail)
  end.

Fixpoint rs_list_to_rocq {T : Type} (xs : ImportedRestrictedSupplyFull.List T) :
    seq T :=
  match xs with
  | ImportedRestrictedSupplyFull.List_nil => [::]
  | ImportedRestrictedSupplyFull.List_cons x tail => x :: rs_list_to_rocq tail
  end.

Definition RsListRel {T : Type} (xsR : seq T)
    (xsL : ImportedRestrictedSupplyFull.List T) : SProp :=
  Lean.eq (rs_list_to_imported xsR) xsL.

Lemma rs_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (rs_list_to_rocq (rs_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma rs_list_target_roundtrip {T : Type}
    (xs : ImportedRestrictedSupplyFull.List T) :
  Lean.eq (rs_list_to_imported (rs_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedRestrictedSupplyFull.List_cons T x) _ _ IH).
Qed.

Definition rs_target_mem {T : Type} (x : T)
    (xs : ImportedRestrictedSupplyFull.List T) : SProp :=
  ImportedRestrictedSupplyFull.Membership_mem T (ImportedRestrictedSupplyFull.List T)
    (ImportedRestrictedSupplyFull.List_instMembership T) xs x.

Definition rs_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedRestrictedSupplyFull.List T) :
  Lean.eq xs ys -> ImportedRestrictedSupplyFull.List_Mem T x xs ->
  ImportedRestrictedSupplyFull.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedRestrictedSupplyFull.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition rs_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedRestrictedSupplyFull.List T) : Logic.eq x y ->
    ImportedRestrictedSupplyFull.List_Mem T x (ImportedRestrictedSupplyFull.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedRestrictedSupplyFull.List_Mem T x (ImportedRestrictedSupplyFull.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedRestrictedSupplyFull.List_Mem_head T x xs
    end.

Definition rs_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition rs_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition rs_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint rs_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedRestrictedSupplyFull.List_Mem T x (rs_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedRestrictedSupplyFull.List_Mem T x (rs_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedRestrictedSupplyFull.List_Mem T x
          (ImportedRestrictedSupplyFull.List_cons T y (rs_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => rs_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedRestrictedSupplyFull.List_Mem_tail T x y _
          (rs_seq_mem_forward x ys H)
      end
  end.

Fixpoint rs_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedRestrictedSupplyFull.List T)
    (H : ImportedRestrictedSupplyFull.List_Mem T x xs) :
    SubNatTruth (x \in rs_list_to_rocq xs) :=
  match H with
  | ImportedRestrictedSupplyFull.List_Mem_head ys =>
      rs_mem_head_truth _ _ (rs_eq_refl_truth T x)
  | ImportedRestrictedSupplyFull.List_Mem_tail y ys Htail =>
      rs_mem_tail_truth _ _
        (rs_imported_mem_decoded x ys Htail)
  end.

Definition rs_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma rs_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedRestrictedSupplyFull.List T) :
  RsListRel xsR xsL ->
  PropSPropRel (x \in xsR) (rs_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold rs_target_mem.
    apply (rs_list_mem_transport x _ _ Hxs).
    apply rs_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (rs_mem_truth_transport x _ _
      (rs_list_source_roundtrip xsR)).
    apply rs_imported_mem_decoded.
    unfold rs_target_mem in Hmem.
    exact (rs_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN rs_bool_source_roundtrip". exact I.
Qed.
Print Assumptions rs_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END rs_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN rs_bool_target_roundtrip". exact I.
Qed.
Print Assumptions rs_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END rs_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN rs_bool_truth_correspondence". exact I.
Qed.
Print Assumptions rs_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END rs_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN rs_list_source_roundtrip". exact I.
Qed.
Print Assumptions rs_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END rs_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN rs_list_target_roundtrip". exact I.
Qed.
Print Assumptions rs_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END rs_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN rs_membership_correspondence". exact I.
Qed.
Print Assumptions rs_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END rs_membership_correspondence". exact I.
Qed.
