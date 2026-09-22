From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ${IMPORTED}.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive ${CAP}False : SProp := .
Inductive ${CAP}True : SProp := ${PREFIX}_true_intro.

Definition ${PREFIX}_false_elim (Q : SProp) (H : ${CAP}False) : Q :=
  match H return Q with end.

Definition ${PREFIX}_false_to_strict (H : ${CAP}False) :
    StrictlyInhabited Logic.False := match H with end.

Definition ${PREFIX}_coq_false_to_target (H : Logic.False) :
    ${IMPORTED}.False := match H return ${IMPORTED}.False with end.

Definition ${PREFIX}_bool_to_imported (b : bool) : ${IMPORTED}.Bool :=
  match b with
  | true => ${IMPORTED}.Bool_true
  | false => ${IMPORTED}.Bool_false
  end.

Definition ${PREFIX}_bool_to_rocq (b : ${IMPORTED}.Bool) : bool :=
  match b with
  | ${IMPORTED}.Bool_true => true
  | ${IMPORTED}.Bool_false => false
  end.

Definition ${CAP}BoolRel (bR : bool) (bL : ${IMPORTED}.Bool) : SProp :=
  Lean.eq (${PREFIX}_bool_to_imported bR) bL.

Lemma ${PREFIX}_bool_source_roundtrip (b : bool) :
  Logic.eq (${PREFIX}_bool_to_rocq (${PREFIX}_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ${PREFIX}_bool_target_roundtrip (b : ${IMPORTED}.Bool) :
  Lean.eq (${PREFIX}_bool_to_imported (${PREFIX}_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition ${PREFIX}_false_ne_true
    (H : Lean.eq ${IMPORTED}.Bool_false ${IMPORTED}.Bool_true) :
    ${CAP}False :=
  match H in Lean.eq _ z return
    match z with
    | ${IMPORTED}.Bool_false => ${CAP}True
    | ${IMPORTED}.Bool_true => ${CAP}False
    end
  with
  | Lean.eq_refl => ${PREFIX}_true_intro
  end.

Lemma ${PREFIX}_bool_truth_correspondence bR bL :
  ${CAP}BoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ${IMPORTED}.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (${PREFIX}_false_to_strict (${PREFIX}_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition ${PREFIX}_decidable_eq (T : eqType) : ${IMPORTED}.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ${IMPORTED}.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ${IMPORTED}.Decidable_isFalse (Lean.eq x y)
        (fun HL => ${PREFIX}_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint ${PREFIX}_list_to_imported {T : Type} (xs : seq T) :
    ${IMPORTED}.List T :=
  match xs with
  | [::] => ${IMPORTED}.List_nil T
  | x :: tail => ${IMPORTED}.List_cons T x
      (${PREFIX}_list_to_imported tail)
  end.

Fixpoint ${PREFIX}_list_to_rocq {T : Type} (xs : ${IMPORTED}.List T) :
    seq T :=
  match xs with
  | ${IMPORTED}.List_nil => [::]
  | ${IMPORTED}.List_cons x tail => x :: ${PREFIX}_list_to_rocq tail
  end.

Definition ${CAP}ListRel {T : Type} (xsR : seq T)
    (xsL : ${IMPORTED}.List T) : SProp :=
  Lean.eq (${PREFIX}_list_to_imported xsR) xsL.

Lemma ${PREFIX}_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (${PREFIX}_list_to_rocq (${PREFIX}_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma ${PREFIX}_list_target_roundtrip {T : Type}
    (xs : ${IMPORTED}.List T) :
  Lean.eq (${PREFIX}_list_to_imported (${PREFIX}_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (${IMPORTED}.List_cons T x) _ _ IH).
Qed.

Definition ${PREFIX}_target_mem {T : Type} (x : T)
    (xs : ${IMPORTED}.List T) : SProp :=
  ${IMPORTED}.Membership_mem T (${IMPORTED}.List T)
    (${IMPORTED}.List_instMembership T) xs x.

Definition ${PREFIX}_list_mem_transport {T : Type} (x : T)
    (xs ys : ${IMPORTED}.List T) :
  Lean.eq xs ys -> ${IMPORTED}.List_Mem T x xs ->
  ${IMPORTED}.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ${IMPORTED}.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition ${PREFIX}_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ${IMPORTED}.List T) : Logic.eq x y ->
    ${IMPORTED}.List_Mem T x (${IMPORTED}.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ${IMPORTED}.List_Mem T x (${IMPORTED}.List_cons T z xs)
    with
    | Logic.eq_refl => ${IMPORTED}.List_Mem_head T x xs
    end.

Definition ${PREFIX}_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition ${PREFIX}_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition ${PREFIX}_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint ${PREFIX}_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ${IMPORTED}.List_Mem T x (${PREFIX}_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ${IMPORTED}.List_Mem T x (${PREFIX}_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ${IMPORTED}.List_Mem T x
          (${IMPORTED}.List_cons T y (${PREFIX}_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => ${PREFIX}_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ${IMPORTED}.List_Mem_tail T x y _
          (${PREFIX}_seq_mem_forward x ys H)
      end
  end.

Fixpoint ${PREFIX}_imported_mem_decoded {T : eqType} (x : T)
    (xs : ${IMPORTED}.List T)
    (H : ${IMPORTED}.List_Mem T x xs) :
    SubNatTruth (x \in ${PREFIX}_list_to_rocq xs) :=
  match H with
  | ${IMPORTED}.List_Mem_head ys =>
      ${PREFIX}_mem_head_truth _ _ (${PREFIX}_eq_refl_truth T x)
  | ${IMPORTED}.List_Mem_tail y ys Htail =>
      ${PREFIX}_mem_tail_truth _ _
        (${PREFIX}_imported_mem_decoded x ys Htail)
  end.

Definition ${PREFIX}_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma ${PREFIX}_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ${IMPORTED}.List T) :
  ${CAP}ListRel xsR xsL ->
  PropSPropRel (x \in xsR) (${PREFIX}_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold ${PREFIX}_target_mem.
    apply (${PREFIX}_list_mem_transport x _ _ Hxs).
    apply ${PREFIX}_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (${PREFIX}_mem_truth_transport x _ _
      (${PREFIX}_list_source_roundtrip xsR)).
    apply ${PREFIX}_imported_mem_decoded.
    unfold ${PREFIX}_target_mem in Hmem.
    exact (${PREFIX}_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ${PREFIX}_bool_source_roundtrip". exact I.
Qed.
Print Assumptions ${PREFIX}_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ${PREFIX}_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ${PREFIX}_bool_target_roundtrip". exact I.
Qed.
Print Assumptions ${PREFIX}_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ${PREFIX}_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ${PREFIX}_bool_truth_correspondence". exact I.
Qed.
Print Assumptions ${PREFIX}_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ${PREFIX}_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ${PREFIX}_list_source_roundtrip". exact I.
Qed.
Print Assumptions ${PREFIX}_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ${PREFIX}_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ${PREFIX}_list_target_roundtrip". exact I.
Qed.
Print Assumptions ${PREFIX}_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ${PREFIX}_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ${PREFIX}_membership_correspondence". exact I.
Qed.
Print Assumptions ${PREFIX}_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ${PREFIX}_membership_correspondence". exact I.
Qed.
