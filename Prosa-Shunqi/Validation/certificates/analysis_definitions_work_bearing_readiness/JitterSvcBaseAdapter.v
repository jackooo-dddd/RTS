(* Re-bound copy of accepted certificates/model_readiness_jitter/JitterSvcBaseAdapter.v for the analysis/facts/behavior/arrivals
   artifact; only the imported module name differs. *)
(* Re-bound copy of the accepted readiness/basic BasicBaseAdapter.v for the
   jitter projection artifact; only module names differ. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedWorkBearingReadiness.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Generated artifact-local adapter.  This file contains proofs, not
    assumptions.  It must be compiled and assumption-audited for the exact
    imported artifact named above. *)

Inductive SvcFalse : SProp := .
Inductive SvcTrue : SProp := svc_true_intro.

Definition svc_false_elim (Q : SProp) (H : SvcFalse) : Q :=
  match H return Q with end.

Definition svc_false_to_strict (H : SvcFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition svc_coq_false_to_target (H : Logic.False) :
    ImportedWorkBearingReadiness.False := match H return ImportedWorkBearingReadiness.False with end.

Definition svc_bool_to_imported (b : bool) : ImportedWorkBearingReadiness.Bool :=
  match b with
  | true => ImportedWorkBearingReadiness.Bool_true
  | false => ImportedWorkBearingReadiness.Bool_false
  end.

Definition svc_bool_to_rocq (b : ImportedWorkBearingReadiness.Bool) : bool :=
  match b with
  | ImportedWorkBearingReadiness.Bool_true => true
  | ImportedWorkBearingReadiness.Bool_false => false
  end.

Definition SvcBoolRel (bR : bool) (bL : ImportedWorkBearingReadiness.Bool) : SProp :=
  Lean.eq (svc_bool_to_imported bR) bL.

Lemma svc_bool_source_roundtrip (b : bool) :
  Logic.eq (svc_bool_to_rocq (svc_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma svc_bool_target_roundtrip (b : ImportedWorkBearingReadiness.Bool) :
  Lean.eq (svc_bool_to_imported (svc_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition svc_false_ne_true
    (H : Lean.eq ImportedWorkBearingReadiness.Bool_false ImportedWorkBearingReadiness.Bool_true) :
    SvcFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedWorkBearingReadiness.Bool_false => SvcTrue
    | ImportedWorkBearingReadiness.Bool_true => SvcFalse
    end
  with
  | Lean.eq_refl => svc_true_intro
  end.

Lemma svc_bool_truth_correspondence bR bL :
  SvcBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedWorkBearingReadiness.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (svc_false_to_strict (svc_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition svc_decidable_eq (T : eqType) : ImportedWorkBearingReadiness.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedWorkBearingReadiness.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedWorkBearingReadiness.Decidable_isFalse (Lean.eq x y)
        (fun HL => svc_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint svc_list_to_imported {T : Type} (xs : seq T) :
    ImportedWorkBearingReadiness.List T :=
  match xs with
  | [::] => ImportedWorkBearingReadiness.List_nil T
  | x :: tail => ImportedWorkBearingReadiness.List_cons T x
      (svc_list_to_imported tail)
  end.

Fixpoint svc_list_to_rocq {T : Type} (xs : ImportedWorkBearingReadiness.List T) :
    seq T :=
  match xs with
  | ImportedWorkBearingReadiness.List_nil => [::]
  | ImportedWorkBearingReadiness.List_cons x tail => x :: svc_list_to_rocq tail
  end.

Definition SvcListRel {T : Type} (xsR : seq T)
    (xsL : ImportedWorkBearingReadiness.List T) : SProp :=
  Lean.eq (svc_list_to_imported xsR) xsL.

Lemma svc_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (svc_list_to_rocq (svc_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma svc_list_target_roundtrip {T : Type}
    (xs : ImportedWorkBearingReadiness.List T) :
  Lean.eq (svc_list_to_imported (svc_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedWorkBearingReadiness.List_cons T x) _ _ IH).
Qed.

Definition svc_target_mem {T : Type} (x : T)
    (xs : ImportedWorkBearingReadiness.List T) : SProp :=
  ImportedWorkBearingReadiness.Membership_mem T (ImportedWorkBearingReadiness.List T)
    (ImportedWorkBearingReadiness.List_instMembership T) xs x.

Definition svc_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedWorkBearingReadiness.List T) :
  Lean.eq xs ys -> ImportedWorkBearingReadiness.List_Mem T x xs ->
  ImportedWorkBearingReadiness.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedWorkBearingReadiness.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition svc_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedWorkBearingReadiness.List T) : Logic.eq x y ->
    ImportedWorkBearingReadiness.List_Mem T x (ImportedWorkBearingReadiness.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedWorkBearingReadiness.List_Mem T x (ImportedWorkBearingReadiness.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedWorkBearingReadiness.List_Mem_head T x xs
    end.

Definition svc_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition svc_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition svc_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint svc_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedWorkBearingReadiness.List_Mem T x (svc_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedWorkBearingReadiness.List_Mem T x (svc_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedWorkBearingReadiness.List_Mem T x
          (ImportedWorkBearingReadiness.List_cons T y (svc_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => svc_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedWorkBearingReadiness.List_Mem_tail T x y _
          (svc_seq_mem_forward x ys H)
      end
  end.

Fixpoint svc_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedWorkBearingReadiness.List T)
    (H : ImportedWorkBearingReadiness.List_Mem T x xs) :
    SubNatTruth (x \in svc_list_to_rocq xs) :=
  match H with
  | ImportedWorkBearingReadiness.List_Mem_head ys =>
      svc_mem_head_truth _ _ (svc_eq_refl_truth T x)
  | ImportedWorkBearingReadiness.List_Mem_tail y ys Htail =>
      svc_mem_tail_truth _ _
        (svc_imported_mem_decoded x ys Htail)
  end.

Definition svc_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma svc_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedWorkBearingReadiness.List T) :
  SvcListRel xsR xsL ->
  PropSPropRel (x \in xsR) (svc_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold svc_target_mem.
    apply (svc_list_mem_transport x _ _ Hxs).
    apply svc_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (svc_mem_truth_transport x _ _
      (svc_list_source_roundtrip xsR)).
    apply svc_imported_mem_decoded.
    unfold svc_target_mem in Hmem.
    exact (svc_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN svc_bool_source_roundtrip". exact I.
Qed.
Print Assumptions svc_bool_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END svc_bool_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN svc_bool_target_roundtrip". exact I.
Qed.
Print Assumptions svc_bool_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END svc_bool_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN svc_bool_truth_correspondence". exact I.
Qed.
Print Assumptions svc_bool_truth_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END svc_bool_truth_correspondence". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN svc_list_source_roundtrip". exact I.
Qed.
Print Assumptions svc_list_source_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END svc_list_source_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN svc_list_target_roundtrip". exact I.
Qed.
Print Assumptions svc_list_target_roundtrip.
Goal Logic.True.
Proof.
  idtac "AUDIT_END svc_list_target_roundtrip". exact I.
Qed.
Goal Logic.True.
Proof.
  idtac "AUDIT_BEGIN svc_membership_correspondence". exact I.
Qed.
Print Assumptions svc_membership_correspondence.
Goal Logic.True.
Proof.
  idtac "AUDIT_END svc_membership_correspondence". exact I.
Qed.
