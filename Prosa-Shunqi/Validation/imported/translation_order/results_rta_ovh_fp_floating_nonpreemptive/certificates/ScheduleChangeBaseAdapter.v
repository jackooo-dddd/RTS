From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaOvhFpFloatingNonpreemptive.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive ScFalse : SProp := .
Inductive ScTrue : SProp := sc_true_intro.

Definition sc_false_elim (Q : SProp) (H : ScFalse) : Q :=
  match H return Q with end.

Definition sc_false_to_strict (H : ScFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition sc_coq_false_to_target (H : Logic.False) :
    ImportedRtaOvhFpFloatingNonpreemptive.False := match H return ImportedRtaOvhFpFloatingNonpreemptive.False with end.

Definition sc_bool_to_imported (b : bool) : ImportedRtaOvhFpFloatingNonpreemptive.Bool :=
  match b with
  | true => ImportedRtaOvhFpFloatingNonpreemptive.Bool_true
  | false => ImportedRtaOvhFpFloatingNonpreemptive.Bool_false
  end.

Definition sc_bool_to_rocq (b : ImportedRtaOvhFpFloatingNonpreemptive.Bool) : bool :=
  match b with
  | ImportedRtaOvhFpFloatingNonpreemptive.Bool_true => true
  | ImportedRtaOvhFpFloatingNonpreemptive.Bool_false => false
  end.

Definition ScBoolRel (bR : bool) (bL : ImportedRtaOvhFpFloatingNonpreemptive.Bool) : SProp :=
  Lean.eq (sc_bool_to_imported bR) bL.

Lemma sc_bool_source_roundtrip (b : bool) :
  Logic.eq (sc_bool_to_rocq (sc_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma sc_bool_target_roundtrip (b : ImportedRtaOvhFpFloatingNonpreemptive.Bool) :
  Lean.eq (sc_bool_to_imported (sc_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition sc_false_ne_true
    (H : Lean.eq ImportedRtaOvhFpFloatingNonpreemptive.Bool_false ImportedRtaOvhFpFloatingNonpreemptive.Bool_true) :
    ScFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedRtaOvhFpFloatingNonpreemptive.Bool_false => ScTrue
    | ImportedRtaOvhFpFloatingNonpreemptive.Bool_true => ScFalse
    end
  with
  | Lean.eq_refl => sc_true_intro
  end.

Lemma sc_bool_truth_correspondence bR bL :
  ScBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedRtaOvhFpFloatingNonpreemptive.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (sc_false_to_strict (sc_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition sc_decidable_eq (T : eqType) : ImportedRtaOvhFpFloatingNonpreemptive.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedRtaOvhFpFloatingNonpreemptive.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedRtaOvhFpFloatingNonpreemptive.Decidable_isFalse (Lean.eq x y)
        (fun HL => sc_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint sc_list_to_imported {T : Type} (xs : seq T) :
    ImportedRtaOvhFpFloatingNonpreemptive.List T :=
  match xs with
  | [::] => ImportedRtaOvhFpFloatingNonpreemptive.List_nil T
  | x :: tail => ImportedRtaOvhFpFloatingNonpreemptive.List_cons T x
      (sc_list_to_imported tail)
  end.

Fixpoint sc_list_to_rocq {T : Type} (xs : ImportedRtaOvhFpFloatingNonpreemptive.List T) :
    seq T :=
  match xs with
  | ImportedRtaOvhFpFloatingNonpreemptive.List_nil => [::]
  | ImportedRtaOvhFpFloatingNonpreemptive.List_cons x tail => x :: sc_list_to_rocq tail
  end.

Definition ScListRel {T : Type} (xsR : seq T)
    (xsL : ImportedRtaOvhFpFloatingNonpreemptive.List T) : SProp :=
  Lean.eq (sc_list_to_imported xsR) xsL.

Lemma sc_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (sc_list_to_rocq (sc_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma sc_list_target_roundtrip {T : Type}
    (xs : ImportedRtaOvhFpFloatingNonpreemptive.List T) :
  Lean.eq (sc_list_to_imported (sc_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedRtaOvhFpFloatingNonpreemptive.List_cons T x) _ _ IH).
Qed.

Definition sc_target_mem {T : Type} (x : T)
    (xs : ImportedRtaOvhFpFloatingNonpreemptive.List T) : SProp :=
  ImportedRtaOvhFpFloatingNonpreemptive.Membership_mem T (ImportedRtaOvhFpFloatingNonpreemptive.List T)
    (ImportedRtaOvhFpFloatingNonpreemptive.List_instMembership T) xs x.

Definition sc_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedRtaOvhFpFloatingNonpreemptive.List T) :
  Lean.eq xs ys -> ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x xs ->
  ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition sc_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedRtaOvhFpFloatingNonpreemptive.List T) : Logic.eq x y ->
    ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x (ImportedRtaOvhFpFloatingNonpreemptive.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x (ImportedRtaOvhFpFloatingNonpreemptive.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedRtaOvhFpFloatingNonpreemptive.List_Mem_head T x xs
    end.

Definition sc_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition sc_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition sc_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint sc_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x (sc_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x (sc_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x
          (ImportedRtaOvhFpFloatingNonpreemptive.List_cons T y (sc_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => sc_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedRtaOvhFpFloatingNonpreemptive.List_Mem_tail T x y _
          (sc_seq_mem_forward x ys H)
      end
  end.

Fixpoint sc_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedRtaOvhFpFloatingNonpreemptive.List T)
    (H : ImportedRtaOvhFpFloatingNonpreemptive.List_Mem T x xs) :
    SubNatTruth (x \in sc_list_to_rocq xs) :=
  match H with
  | ImportedRtaOvhFpFloatingNonpreemptive.List_Mem_head ys =>
      sc_mem_head_truth _ _ (sc_eq_refl_truth T x)
  | ImportedRtaOvhFpFloatingNonpreemptive.List_Mem_tail y ys Htail =>
      sc_mem_tail_truth _ _
        (sc_imported_mem_decoded x ys Htail)
  end.

Definition sc_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma sc_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedRtaOvhFpFloatingNonpreemptive.List T) :
  ScListRel xsR xsL ->
  PropSPropRel (x \in xsR) (sc_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold sc_target_mem.
    apply (sc_list_mem_transport x _ _ Hxs).
    apply sc_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (sc_mem_truth_transport x _ _
      (sc_list_source_roundtrip xsR)).
    apply sc_imported_mem_decoded.
    unfold sc_target_mem in Hmem.
    exact (sc_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sc_bool_source_roundtrip". exact I.
Qed.
Print Assumptions sc_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sc_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sc_bool_target_roundtrip". exact I.
Qed.
Print Assumptions sc_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sc_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sc_bool_truth_correspondence". exact I.
Qed.
Print Assumptions sc_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sc_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sc_list_source_roundtrip". exact I.
Qed.
Print Assumptions sc_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sc_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sc_list_target_roundtrip". exact I.
Qed.
Print Assumptions sc_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sc_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN sc_membership_correspondence". exact I.
Qed.
Print Assumptions sc_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END sc_membership_correspondence". exact I.
Qed.
