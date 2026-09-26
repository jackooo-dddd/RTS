(* Re-bound copy of accepted certificates/analysis_facts_model_arrival_curves/ArrivalsSeqBaseAdapter.v for the
   model/aggregate/service_of_jobs artifact; only the imported module name differs. *)
(* Re-bound copy of accepted certificates/model_task_arrivals/ArrivalsSeqBaseAdapter.v for the analysis/facts/behavior/arrivals
   artifact; only the imported module name differs. *)
(* Re-bound copy of the accepted behavior/arrival_sequence ArrivalSequenceBaseAdapter.v
   for the model/task/arrivals artifact; only module names differ. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedServiceOfJobs.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive ArFalse : SProp := .
Inductive ArTrue : SProp := ar_true_intro.

Definition ar_false_elim (Q : SProp) (H : ArFalse) : Q :=
  match H return Q with end.

Definition ar_false_to_strict (H : ArFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition ar_coq_false_to_target (H : Logic.False) :
    ImportedServiceOfJobs.False := match H return ImportedServiceOfJobs.False with end.

Definition ar_bool_to_imported (b : bool) : ImportedServiceOfJobs.Bool :=
  match b with
  | true => ImportedServiceOfJobs.Bool_true
  | false => ImportedServiceOfJobs.Bool_false
  end.

Definition ar_bool_to_rocq (b : ImportedServiceOfJobs.Bool) : bool :=
  match b with
  | ImportedServiceOfJobs.Bool_true => true
  | ImportedServiceOfJobs.Bool_false => false
  end.

Definition ArBoolRel (bR : bool) (bL : ImportedServiceOfJobs.Bool) : SProp :=
  Lean.eq (ar_bool_to_imported bR) bL.

Lemma ar_bool_source_roundtrip (b : bool) :
  Logic.eq (ar_bool_to_rocq (ar_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ar_bool_target_roundtrip (b : ImportedServiceOfJobs.Bool) :
  Lean.eq (ar_bool_to_imported (ar_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition ar_false_ne_true
    (H : Lean.eq ImportedServiceOfJobs.Bool_false ImportedServiceOfJobs.Bool_true) :
    ArFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedServiceOfJobs.Bool_false => ArTrue
    | ImportedServiceOfJobs.Bool_true => ArFalse
    end
  with
  | Lean.eq_refl => ar_true_intro
  end.

Lemma ar_bool_truth_correspondence bR bL :
  ArBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedServiceOfJobs.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (ar_false_to_strict (ar_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition ar_decidable_eq (T : eqType) : ImportedServiceOfJobs.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedServiceOfJobs.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedServiceOfJobs.Decidable_isFalse (Lean.eq x y)
        (fun HL => ar_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint ar_list_to_imported {T : Type} (xs : seq T) :
    ImportedServiceOfJobs.List T :=
  match xs with
  | [::] => ImportedServiceOfJobs.List_nil T
  | x :: tail => ImportedServiceOfJobs.List_cons T x
      (ar_list_to_imported tail)
  end.

Fixpoint ar_list_to_rocq {T : Type} (xs : ImportedServiceOfJobs.List T) :
    seq T :=
  match xs with
  | ImportedServiceOfJobs.List_nil => [::]
  | ImportedServiceOfJobs.List_cons x tail => x :: ar_list_to_rocq tail
  end.

Definition ArListRel {T : Type} (xsR : seq T)
    (xsL : ImportedServiceOfJobs.List T) : SProp :=
  Lean.eq (ar_list_to_imported xsR) xsL.

Lemma ar_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (ar_list_to_rocq (ar_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma ar_list_target_roundtrip {T : Type}
    (xs : ImportedServiceOfJobs.List T) :
  Lean.eq (ar_list_to_imported (ar_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedServiceOfJobs.List_cons T x) _ _ IH).
Qed.

Definition ar_target_mem {T : Type} (x : T)
    (xs : ImportedServiceOfJobs.List T) : SProp :=
  ImportedServiceOfJobs.Membership_mem T (ImportedServiceOfJobs.List T)
    (ImportedServiceOfJobs.List_instMembership T) xs x.

Definition ar_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedServiceOfJobs.List T) :
  Lean.eq xs ys -> ImportedServiceOfJobs.List_Mem T x xs ->
  ImportedServiceOfJobs.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedServiceOfJobs.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition ar_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedServiceOfJobs.List T) : Logic.eq x y ->
    ImportedServiceOfJobs.List_Mem T x (ImportedServiceOfJobs.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedServiceOfJobs.List_Mem T x (ImportedServiceOfJobs.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedServiceOfJobs.List_Mem_head T x xs
    end.

Definition ar_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition ar_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition ar_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint ar_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedServiceOfJobs.List_Mem T x (ar_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedServiceOfJobs.List_Mem T x (ar_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedServiceOfJobs.List_Mem T x
          (ImportedServiceOfJobs.List_cons T y (ar_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => ar_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedServiceOfJobs.List_Mem_tail T x y _
          (ar_seq_mem_forward x ys H)
      end
  end.

Fixpoint ar_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedServiceOfJobs.List T)
    (H : ImportedServiceOfJobs.List_Mem T x xs) :
    SubNatTruth (x \in ar_list_to_rocq xs) :=
  match H with
  | ImportedServiceOfJobs.List_Mem_head ys =>
      ar_mem_head_truth _ _ (ar_eq_refl_truth T x)
  | ImportedServiceOfJobs.List_Mem_tail y ys Htail =>
      ar_mem_tail_truth _ _
        (ar_imported_mem_decoded x ys Htail)
  end.

Definition ar_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma ar_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedServiceOfJobs.List T) :
  ArListRel xsR xsL ->
  PropSPropRel (x \in xsR) (ar_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold ar_target_mem.
    apply (ar_list_mem_transport x _ _ Hxs).
    apply ar_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (ar_mem_truth_transport x _ _
      (ar_list_source_roundtrip xsR)).
    apply ar_imported_mem_decoded.
    unfold ar_target_mem in Hmem.
    exact (ar_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_bool_source_roundtrip". exact I.
Qed.
Print Assumptions ar_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_bool_target_roundtrip". exact I.
Qed.
Print Assumptions ar_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_bool_truth_correspondence". exact I.
Qed.
Print Assumptions ar_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_list_source_roundtrip". exact I.
Qed.
Print Assumptions ar_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_list_target_roundtrip". exact I.
Qed.
Print Assumptions ar_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN ar_membership_correspondence". exact I.
Qed.
Print Assumptions ar_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END ar_membership_correspondence". exact I.
Qed.
