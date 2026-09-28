(* Re-bound copy of accepted imported/translation_order/abstract_definitions/certificates/AbstractDefinitionsBaseAdapter.v for the busy_sbf artifact; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskIntraInterferenceBound.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive AdFalse : SProp := .
Inductive AdTrue : SProp := ad_true_intro.

Definition ad_false_elim (Q : SProp) (H : AdFalse) : Q :=
  match H return Q with end.

Definition ad_false_to_strict (H : AdFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition ad_coq_false_to_target (H : Logic.False) :
    ImportedTaskIntraInterferenceBound.False := match H return ImportedTaskIntraInterferenceBound.False with end.

Definition ad_bool_to_imported (b : bool) : ImportedTaskIntraInterferenceBound.Bool :=
  match b with
  | true => ImportedTaskIntraInterferenceBound.Bool_true
  | false => ImportedTaskIntraInterferenceBound.Bool_false
  end.

Definition ad_bool_to_rocq (b : ImportedTaskIntraInterferenceBound.Bool) : bool :=
  match b with
  | ImportedTaskIntraInterferenceBound.Bool_true => true
  | ImportedTaskIntraInterferenceBound.Bool_false => false
  end.

Definition AdBoolRel (bR : bool) (bL : ImportedTaskIntraInterferenceBound.Bool) : SProp :=
  Lean.eq (ad_bool_to_imported bR) bL.

Lemma ad_bool_source_roundtrip (b : bool) :
  Logic.eq (ad_bool_to_rocq (ad_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ad_bool_target_roundtrip (b : ImportedTaskIntraInterferenceBound.Bool) :
  Lean.eq (ad_bool_to_imported (ad_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition ad_false_ne_true
    (H : Lean.eq ImportedTaskIntraInterferenceBound.Bool_false ImportedTaskIntraInterferenceBound.Bool_true) :
    AdFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedTaskIntraInterferenceBound.Bool_false => AdTrue
    | ImportedTaskIntraInterferenceBound.Bool_true => AdFalse
    end
  with
  | Lean.eq_refl => ad_true_intro
  end.

Lemma ad_bool_truth_correspondence bR bL :
  AdBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedTaskIntraInterferenceBound.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (ad_false_to_strict (ad_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition ad_decidable_eq (T : eqType) : ImportedTaskIntraInterferenceBound.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedTaskIntraInterferenceBound.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedTaskIntraInterferenceBound.Decidable_isFalse (Lean.eq x y)
        (fun HL => ad_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint ad_list_to_imported {T : Type} (xs : seq T) :
    ImportedTaskIntraInterferenceBound.List T :=
  match xs with
  | [::] => ImportedTaskIntraInterferenceBound.List_nil T
  | x :: tail => ImportedTaskIntraInterferenceBound.List_cons T x
      (ad_list_to_imported tail)
  end.

Fixpoint ad_list_to_rocq {T : Type} (xs : ImportedTaskIntraInterferenceBound.List T) :
    seq T :=
  match xs with
  | ImportedTaskIntraInterferenceBound.List_nil => [::]
  | ImportedTaskIntraInterferenceBound.List_cons x tail => x :: ad_list_to_rocq tail
  end.

Definition AdListRel {T : Type} (xsR : seq T)
    (xsL : ImportedTaskIntraInterferenceBound.List T) : SProp :=
  Lean.eq (ad_list_to_imported xsR) xsL.

Lemma ad_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (ad_list_to_rocq (ad_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma ad_list_target_roundtrip {T : Type}
    (xs : ImportedTaskIntraInterferenceBound.List T) :
  Lean.eq (ad_list_to_imported (ad_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedTaskIntraInterferenceBound.List_cons T x) _ _ IH).
Qed.

Definition ad_target_mem {T : Type} (x : T)
    (xs : ImportedTaskIntraInterferenceBound.List T) : SProp :=
  ImportedTaskIntraInterferenceBound.Membership_mem T (ImportedTaskIntraInterferenceBound.List T)
    (ImportedTaskIntraInterferenceBound.List_instMembership T) xs x.

Definition ad_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedTaskIntraInterferenceBound.List T) :
  Lean.eq xs ys -> ImportedTaskIntraInterferenceBound.List_Mem T x xs ->
  ImportedTaskIntraInterferenceBound.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedTaskIntraInterferenceBound.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition ad_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedTaskIntraInterferenceBound.List T) : Logic.eq x y ->
    ImportedTaskIntraInterferenceBound.List_Mem T x (ImportedTaskIntraInterferenceBound.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedTaskIntraInterferenceBound.List_Mem T x (ImportedTaskIntraInterferenceBound.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedTaskIntraInterferenceBound.List_Mem_head T x xs
    end.

Definition ad_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition ad_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition ad_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint ad_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedTaskIntraInterferenceBound.List_Mem T x (ad_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedTaskIntraInterferenceBound.List_Mem T x (ad_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedTaskIntraInterferenceBound.List_Mem T x
          (ImportedTaskIntraInterferenceBound.List_cons T y (ad_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => ad_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedTaskIntraInterferenceBound.List_Mem_tail T x y _
          (ad_seq_mem_forward x ys H)
      end
  end.

Fixpoint ad_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedTaskIntraInterferenceBound.List T)
    (H : ImportedTaskIntraInterferenceBound.List_Mem T x xs) :
    SubNatTruth (x \in ad_list_to_rocq xs) :=
  match H with
  | ImportedTaskIntraInterferenceBound.List_Mem_head ys =>
      ad_mem_head_truth _ _ (ad_eq_refl_truth T x)
  | ImportedTaskIntraInterferenceBound.List_Mem_tail y ys Htail =>
      ad_mem_tail_truth _ _
        (ad_imported_mem_decoded x ys Htail)
  end.

Definition ad_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma ad_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedTaskIntraInterferenceBound.List T) :
  AdListRel xsR xsL ->
  PropSPropRel (x \in xsR) (ad_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold ad_target_mem.
    apply (ad_list_mem_transport x _ _ Hxs).
    apply ad_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (ad_mem_truth_transport x _ _
      (ad_list_source_roundtrip xsR)).
    apply ad_imported_mem_decoded.
    unfold ad_target_mem in Hmem.
    exact (ad_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ad_bool_source_roundtrip". exact I.
Qed.
Print Assumptions ad_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ad_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ad_bool_target_roundtrip". exact I.
Qed.
Print Assumptions ad_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ad_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ad_bool_truth_correspondence". exact I.
Qed.
Print Assumptions ad_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ad_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ad_list_source_roundtrip". exact I.
Qed.
Print Assumptions ad_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ad_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ad_list_target_roundtrip". exact I.
Qed.
Print Assumptions ad_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ad_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ad_membership_correspondence". exact I.
Qed.
Print Assumptions ad_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ad_membership_correspondence". exact I.
Qed.
