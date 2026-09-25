From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsBehaviorSupply.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive SchFalse : SProp := .
Inductive SchTrue : SProp := sch_true_intro.

Definition sch_false_elim (Q : SProp) (H : SchFalse) : Q :=
  match H return Q with end.

Definition sch_false_to_strict (H : SchFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition sch_coq_false_to_target (H : Logic.False) :
    ImportedFactsBehaviorSupply.False := match H return ImportedFactsBehaviorSupply.False with end.

Definition sch_bool_to_imported (b : bool) : ImportedFactsBehaviorSupply.Bool :=
  match b with
  | true => ImportedFactsBehaviorSupply.Bool_true
  | false => ImportedFactsBehaviorSupply.Bool_false
  end.

Definition sch_bool_to_rocq (b : ImportedFactsBehaviorSupply.Bool) : bool :=
  match b with
  | ImportedFactsBehaviorSupply.Bool_true => true
  | ImportedFactsBehaviorSupply.Bool_false => false
  end.

Definition SchBoolRel (bR : bool) (bL : ImportedFactsBehaviorSupply.Bool) : SProp :=
  Lean.eq (sch_bool_to_imported bR) bL.

Lemma sch_bool_source_roundtrip (b : bool) :
  Logic.eq (sch_bool_to_rocq (sch_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma sch_bool_target_roundtrip (b : ImportedFactsBehaviorSupply.Bool) :
  Lean.eq (sch_bool_to_imported (sch_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition sch_false_ne_true
    (H : Lean.eq ImportedFactsBehaviorSupply.Bool_false ImportedFactsBehaviorSupply.Bool_true) :
    SchFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedFactsBehaviorSupply.Bool_false => SchTrue
    | ImportedFactsBehaviorSupply.Bool_true => SchFalse
    end
  with
  | Lean.eq_refl => sch_true_intro
  end.

Lemma sch_bool_truth_correspondence bR bL :
  SchBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedFactsBehaviorSupply.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (sch_false_to_strict (sch_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition sch_decidable_eq (T : eqType) : ImportedFactsBehaviorSupply.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedFactsBehaviorSupply.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedFactsBehaviorSupply.Decidable_isFalse (Lean.eq x y)
        (fun HL => sch_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint sch_list_to_imported {T : Type} (xs : seq T) :
    ImportedFactsBehaviorSupply.List T :=
  match xs with
  | [::] => ImportedFactsBehaviorSupply.List_nil T
  | x :: tail => ImportedFactsBehaviorSupply.List_cons T x
      (sch_list_to_imported tail)
  end.

Fixpoint sch_list_to_rocq {T : Type} (xs : ImportedFactsBehaviorSupply.List T) :
    seq T :=
  match xs with
  | ImportedFactsBehaviorSupply.List_nil => [::]
  | ImportedFactsBehaviorSupply.List_cons x tail => x :: sch_list_to_rocq tail
  end.

Definition SchListRel {T : Type} (xsR : seq T)
    (xsL : ImportedFactsBehaviorSupply.List T) : SProp :=
  Lean.eq (sch_list_to_imported xsR) xsL.

Lemma sch_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (sch_list_to_rocq (sch_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma sch_list_target_roundtrip {T : Type}
    (xs : ImportedFactsBehaviorSupply.List T) :
  Lean.eq (sch_list_to_imported (sch_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedFactsBehaviorSupply.List_cons T x) _ _ IH).
Qed.

Definition sch_target_mem {T : Type} (x : T)
    (xs : ImportedFactsBehaviorSupply.List T) : SProp :=
  ImportedFactsBehaviorSupply.Membership_mem T (ImportedFactsBehaviorSupply.List T)
    (ImportedFactsBehaviorSupply.List_instMembership T) xs x.

Definition sch_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedFactsBehaviorSupply.List T) :
  Lean.eq xs ys -> ImportedFactsBehaviorSupply.List_Mem T x xs ->
  ImportedFactsBehaviorSupply.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedFactsBehaviorSupply.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition sch_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedFactsBehaviorSupply.List T) : Logic.eq x y ->
    ImportedFactsBehaviorSupply.List_Mem T x (ImportedFactsBehaviorSupply.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedFactsBehaviorSupply.List_Mem T x (ImportedFactsBehaviorSupply.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedFactsBehaviorSupply.List_Mem_head T x xs
    end.

Definition sch_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition sch_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition sch_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint sch_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedFactsBehaviorSupply.List_Mem T x (sch_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedFactsBehaviorSupply.List_Mem T x (sch_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedFactsBehaviorSupply.List_Mem T x
          (ImportedFactsBehaviorSupply.List_cons T y (sch_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => sch_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedFactsBehaviorSupply.List_Mem_tail T x y _
          (sch_seq_mem_forward x ys H)
      end
  end.

Fixpoint sch_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedFactsBehaviorSupply.List T)
    (H : ImportedFactsBehaviorSupply.List_Mem T x xs) :
    SubNatTruth (x \in sch_list_to_rocq xs) :=
  match H with
  | ImportedFactsBehaviorSupply.List_Mem_head ys =>
      sch_mem_head_truth _ _ (sch_eq_refl_truth T x)
  | ImportedFactsBehaviorSupply.List_Mem_tail y ys Htail =>
      sch_mem_tail_truth _ _
        (sch_imported_mem_decoded x ys Htail)
  end.

Definition sch_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma sch_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedFactsBehaviorSupply.List T) :
  SchListRel xsR xsL ->
  PropSPropRel (x \in xsR) (sch_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold sch_target_mem.
    apply (sch_list_mem_transport x _ _ Hxs).
    apply sch_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (sch_mem_truth_transport x _ _
      (sch_list_source_roundtrip xsR)).
    apply sch_imported_mem_decoded.
    unfold sch_target_mem in Hmem.
    exact (sch_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sch_bool_source_roundtrip". exact I.
Qed.
Print Assumptions sch_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sch_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sch_bool_target_roundtrip". exact I.
Qed.
Print Assumptions sch_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sch_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sch_bool_truth_correspondence". exact I.
Qed.
Print Assumptions sch_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sch_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sch_list_source_roundtrip". exact I.
Qed.
Print Assumptions sch_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sch_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sch_list_target_roundtrip". exact I.
Qed.
Print Assumptions sch_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sch_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sch_membership_correspondence". exact I.
Qed.
Print Assumptions sch_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sch_membership_correspondence". exact I.
Qed.
