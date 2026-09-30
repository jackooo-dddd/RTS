(* Copy of the accepted-proof-source certificates/utility_foundation/LcmseqBaseAdapter.v, re-bound to this export: the imported module is
   this file's, the validation interface namespace is LcmseqSpecInterface and the source module is the extracted
   LcmseqSemanticSource; its Print Assumptions commands are dropped. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedHyperperiod.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive LcmseqFalse : SProp := .
Inductive LcmseqTrue : SProp := lcmseq_true_intro.

Definition lcmseq_false_elim (Q : SProp) (H : LcmseqFalse) : Q :=
  match H return Q with end.

Definition lcmseq_false_to_strict (H : LcmseqFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition lcmseq_coq_false_to_target (H : Logic.False) :
    ImportedHyperperiod.False := match H return ImportedHyperperiod.False with end.

Definition lcmseq_bool_to_imported (b : bool) : ImportedHyperperiod.Bool :=
  match b with
  | true => ImportedHyperperiod.Bool_true
  | false => ImportedHyperperiod.Bool_false
  end.

Definition lcmseq_bool_to_rocq (b : ImportedHyperperiod.Bool) : bool :=
  match b with
  | ImportedHyperperiod.Bool_true => true
  | ImportedHyperperiod.Bool_false => false
  end.

Definition LcmseqBoolRel (bR : bool) (bL : ImportedHyperperiod.Bool) : SProp :=
  Lean.eq (lcmseq_bool_to_imported bR) bL.

Lemma lcmseq_bool_source_roundtrip (b : bool) :
  Logic.eq (lcmseq_bool_to_rocq (lcmseq_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma lcmseq_bool_target_roundtrip (b : ImportedHyperperiod.Bool) :
  Lean.eq (lcmseq_bool_to_imported (lcmseq_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition lcmseq_false_ne_true
    (H : Lean.eq ImportedHyperperiod.Bool_false ImportedHyperperiod.Bool_true) :
    LcmseqFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedHyperperiod.Bool_false => LcmseqTrue
    | ImportedHyperperiod.Bool_true => LcmseqFalse
    end
  with
  | Lean.eq_refl => lcmseq_true_intro
  end.

Lemma lcmseq_bool_truth_correspondence bR bL :
  LcmseqBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedHyperperiod.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (lcmseq_false_to_strict (lcmseq_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition lcmseq_decidable_eq (T : eqType) : ImportedHyperperiod.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedHyperperiod.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedHyperperiod.Decidable_isFalse (Lean.eq x y)
        (fun HL => lcmseq_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint lcmseq_list_to_imported {T : Type} (xs : seq T) :
    ImportedHyperperiod.List T :=
  match xs with
  | [::] => ImportedHyperperiod.List_nil T
  | x :: tail => ImportedHyperperiod.List_cons T x
      (lcmseq_list_to_imported tail)
  end.

Fixpoint lcmseq_list_to_rocq {T : Type} (xs : ImportedHyperperiod.List T) :
    seq T :=
  match xs with
  | ImportedHyperperiod.List_nil => [::]
  | ImportedHyperperiod.List_cons x tail => x :: lcmseq_list_to_rocq tail
  end.

Definition LcmseqListRel {T : Type} (xsR : seq T)
    (xsL : ImportedHyperperiod.List T) : SProp :=
  Lean.eq (lcmseq_list_to_imported xsR) xsL.

Lemma lcmseq_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (lcmseq_list_to_rocq (lcmseq_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma lcmseq_list_target_roundtrip {T : Type}
    (xs : ImportedHyperperiod.List T) :
  Lean.eq (lcmseq_list_to_imported (lcmseq_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedHyperperiod.List_cons T x) _ _ IH).
Qed.

Definition lcmseq_target_mem {T : Type} (x : T)
    (xs : ImportedHyperperiod.List T) : SProp :=
  ImportedHyperperiod.Membership_mem T (ImportedHyperperiod.List T)
    (ImportedHyperperiod.List_instMembership T) xs x.

Definition lcmseq_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedHyperperiod.List T) :
  Lean.eq xs ys -> ImportedHyperperiod.List_Mem T x xs ->
  ImportedHyperperiod.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedHyperperiod.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition lcmseq_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedHyperperiod.List T) : Logic.eq x y ->
    ImportedHyperperiod.List_Mem T x (ImportedHyperperiod.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedHyperperiod.List_Mem T x (ImportedHyperperiod.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedHyperperiod.List_Mem_head T x xs
    end.

Definition lcmseq_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition lcmseq_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition lcmseq_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint lcmseq_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedHyperperiod.List_Mem T x (lcmseq_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedHyperperiod.List_Mem T x (lcmseq_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedHyperperiod.List_Mem T x
          (ImportedHyperperiod.List_cons T y (lcmseq_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => lcmseq_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedHyperperiod.List_Mem_tail T x y _
          (lcmseq_seq_mem_forward x ys H)
      end
  end.

Fixpoint lcmseq_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedHyperperiod.List T)
    (H : ImportedHyperperiod.List_Mem T x xs) :
    SubNatTruth (x \in lcmseq_list_to_rocq xs) :=
  match H with
  | ImportedHyperperiod.List_Mem_head ys =>
      lcmseq_mem_head_truth _ _ (lcmseq_eq_refl_truth T x)
  | ImportedHyperperiod.List_Mem_tail y ys Htail =>
      lcmseq_mem_tail_truth _ _
        (lcmseq_imported_mem_decoded x ys Htail)
  end.

Definition lcmseq_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma lcmseq_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedHyperperiod.List T) :
  LcmseqListRel xsR xsL ->
  PropSPropRel (x \in xsR) (lcmseq_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold lcmseq_target_mem.
    apply (lcmseq_list_mem_transport x _ _ Hxs).
    apply lcmseq_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (lcmseq_mem_truth_transport x _ _
      (lcmseq_list_source_roundtrip xsR)).
    apply lcmseq_imported_mem_decoded.
    unfold lcmseq_target_mem in Hmem.
    exact (lcmseq_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN lcmseq_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_END lcmseq_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN lcmseq_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_END lcmseq_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN lcmseq_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_END lcmseq_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN lcmseq_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_END lcmseq_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN lcmseq_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_END lcmseq_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN lcmseq_membership_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_END lcmseq_membership_correspondence". exact I.
Qed.
