(* List operations at the concrete (universe-0) list copies of this export: the accepted
   certificates/analysis_abstract_abstract_rta/ArrivalsSeqBaseAdapter.v together with the membership and uniqueness
   blocks of the accepted ArrivalsSeqOperations.v (ar_decide_bool_correspondence, ar_decide_mem_related,
   ar_uniq_correspondence and their helpers), with the imported list constants renamed to this export's concrete copies
   (List_inst1, List_Mem_inst1, List_Nodup_inst1, List_Pairwise_*_inst1, Membership_mem_inst3, …).  Proofs unchanged. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsJobConstructor.
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
    ImportedFactsJobConstructor.False := match H return ImportedFactsJobConstructor.False with end.

Definition ar_bool_to_imported (b : bool) : ImportedFactsJobConstructor.Bool :=
  match b with
  | true => ImportedFactsJobConstructor.Bool_true
  | false => ImportedFactsJobConstructor.Bool_false
  end.

Definition ar_bool_to_rocq (b : ImportedFactsJobConstructor.Bool) : bool :=
  match b with
  | ImportedFactsJobConstructor.Bool_true => true
  | ImportedFactsJobConstructor.Bool_false => false
  end.

Definition ArBoolRel (bR : bool) (bL : ImportedFactsJobConstructor.Bool) : SProp :=
  Lean.eq (ar_bool_to_imported bR) bL.

Lemma ar_bool_source_roundtrip (b : bool) :
  Logic.eq (ar_bool_to_rocq (ar_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ar_bool_target_roundtrip (b : ImportedFactsJobConstructor.Bool) :
  Lean.eq (ar_bool_to_imported (ar_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition ar_false_ne_true
    (H : Lean.eq ImportedFactsJobConstructor.Bool_false ImportedFactsJobConstructor.Bool_true) :
    ArFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedFactsJobConstructor.Bool_false => ArTrue
    | ImportedFactsJobConstructor.Bool_true => ArFalse
    end
  with
  | Lean.eq_refl => ar_true_intro
  end.

Lemma ar_bool_truth_correspondence bR bL :
  ArBoolRel bR bL ->
  PropSPropRel (is_true bR) (Lean.eq bL ImportedFactsJobConstructor.Bool_true).
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

Definition ar_decidable_eq (T : eqType) : ImportedFactsJobConstructor.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedFactsJobConstructor.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedFactsJobConstructor.Decidable_isFalse (Lean.eq x y)
        (fun HL => ar_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint ar_list_to_imported {T : Type} (xs : seq T) :
    ImportedFactsJobConstructor.List_inst1 T :=
  match xs with
  | [::] => ImportedFactsJobConstructor.List_nil_inst1 T
  | x :: tail => ImportedFactsJobConstructor.List_cons_inst1 T x
      (ar_list_to_imported tail)
  end.

Fixpoint ar_list_to_rocq {T : Type} (xs : ImportedFactsJobConstructor.List_inst1 T) :
    seq T :=
  match xs with
  | ImportedFactsJobConstructor.List_nil_inst1 => [::]
  | ImportedFactsJobConstructor.List_cons_inst1 x tail => x :: ar_list_to_rocq tail
  end.

Definition ArListRel {T : Type} (xsR : seq T)
    (xsL : ImportedFactsJobConstructor.List_inst1 T) : SProp :=
  Lean.eq (ar_list_to_imported xsR) xsL.

Lemma ar_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (ar_list_to_rocq (ar_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma ar_list_target_roundtrip {T : Type}
    (xs : ImportedFactsJobConstructor.List_inst1 T) :
  Lean.eq (ar_list_to_imported (ar_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedFactsJobConstructor.List_cons_inst1 T x) _ _ IH).
Qed.

Definition ar_target_mem {T : Type} (x : T)
    (xs : ImportedFactsJobConstructor.List_inst1 T) : SProp :=
  ImportedFactsJobConstructor.Membership_mem_inst3 T (ImportedFactsJobConstructor.List_inst1 T)
    (ImportedFactsJobConstructor.List_instMembership_inst1 T) xs x.

Definition ar_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedFactsJobConstructor.List_inst1 T) :
  Lean.eq xs ys -> ImportedFactsJobConstructor.List_Mem_inst1 T x xs ->
  ImportedFactsJobConstructor.List_Mem_inst1 T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedFactsJobConstructor.List_Mem_inst1 T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition ar_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedFactsJobConstructor.List_inst1 T) : Logic.eq x y ->
    ImportedFactsJobConstructor.List_Mem_inst1 T x (ImportedFactsJobConstructor.List_cons_inst1 T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedFactsJobConstructor.List_Mem_inst1 T x (ImportedFactsJobConstructor.List_cons_inst1 T z xs)
    with
    | Logic.eq_refl => ImportedFactsJobConstructor.List_Mem_head_inst1 T x xs
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
    ImportedFactsJobConstructor.List_Mem_inst1 T x (ar_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedFactsJobConstructor.List_Mem_inst1 T x (ar_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedFactsJobConstructor.List_Mem_inst1 T x
          (ImportedFactsJobConstructor.List_cons_inst1 T y (ar_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => ar_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedFactsJobConstructor.List_Mem_tail_inst1 T x y _
          (ar_seq_mem_forward x ys H)
      end
  end.

Fixpoint ar_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedFactsJobConstructor.List_inst1 T)
    (H : ImportedFactsJobConstructor.List_Mem_inst1 T x xs) :
    SubNatTruth (x \in ar_list_to_rocq xs) :=
  match H with
  | ImportedFactsJobConstructor.List_Mem_head_inst1 ys =>
      ar_mem_head_truth _ _ (ar_eq_refl_truth T x)
  | ImportedFactsJobConstructor.List_Mem_tail_inst1 y ys Htail =>
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
    (xsR : seq T) (xsL : ImportedFactsJobConstructor.List_inst1 T) :
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

(** ** Decidable membership and uniqueness (from the accepted ArrivalsSeqOperations.v) *)

Definition ar_target_false_elim (Q : SProp)
    (H : ImportedFactsJobConstructor.False) : Q :=
  match H return Q with end.

Definition ar_target_false_to_strict
    (H : ImportedFactsJobConstructor.False) : StrictlyInhabited Logic.False :=
  match H with end.

Lemma ar_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedFactsJobConstructor.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  ArBoolRel b (ImportedFactsJobConstructor.Decidable_decide Q d).
Proof.
  intro Hrel. unfold ArBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (ar_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ar_target_false_elim _ (ar_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Definition ar_target_decide_mem (T : eqType) (x : T)
    (xs : ImportedFactsJobConstructor.List_inst1 T) : ImportedFactsJobConstructor.Bool :=
  ImportedFactsJobConstructor.Decidable_decide (ar_target_mem x xs)
    (ImportedFactsJobConstructor.List_instDecidableMemOfLawfulBEq_inst1 T
      (ImportedFactsJobConstructor.instBEqOfDecidableEq_inst1 T (ar_decidable_eq T))
      (ImportedFactsJobConstructor.instLawfulBEq_inst1 T (ar_decidable_eq T)) x xs).

Lemma ar_decide_mem_related (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedFactsJobConstructor.List_inst1 T) :
  ArListRel xsR xsL ->
  ArBoolRel (x \in xsR) (ar_target_decide_mem T x xsL).
Proof.
  intro Hxs. apply ar_decide_bool_correspondence.
  exact (ar_membership_correspondence T x xsR xsL Hxs).
Qed.

Definition ar_nodup_transport {T : Type}
    (xs ys : ImportedFactsJobConstructor.List_inst1 T) :
  Lean.eq xs ys -> ImportedFactsJobConstructor.List_Nodup_inst1 T xs ->
  ImportedFactsJobConstructor.List_Nodup_inst1 T ys :=
  fun Hxy H =>
    match Hxy in Lean.eq _ zs return
      ImportedFactsJobConstructor.List_Nodup_inst1 T zs with
    | Lean.eq_refl => H
    end.

Definition ar_and_left_truth (a b : bool) :
    SubNatTruth (a && b) -> SubNatTruth a :=
  match a, b return SubNatTruth (a && b) -> SubNatTruth a with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => fun H => H
  end.

Definition ar_and_right_truth (a b : bool) :
    SubNatTruth (a && b) -> SubNatTruth b :=
  match a, b return SubNatTruth (a && b) -> SubNatTruth b with
  | true, true => fun _ => sub_nat_truth_intro
  | true, false => fun H => H
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Definition ar_neg_mem_contra (b : bool) :
    SubNatTruth (~~ b) -> SubNatTruth b -> ImportedFactsJobConstructor.False :=
  match b return SubNatTruth (~~ b) -> SubNatTruth b ->
      ImportedFactsJobConstructor.False with
  | true => fun H _ => match H with end
  | false => fun _ H => match H with end
  end.

Fixpoint ar_uniq_truth_forward (T : eqType) (xs : seq T) :
    SubNatTruth (uniq xs) ->
    ImportedFactsJobConstructor.List_Nodup_inst1 T (ar_list_to_imported xs).
Proof.
  destruct xs as [|x xs].
  - intro Hnil.
    exact (ImportedFactsJobConstructor.List_Pairwise_nil_inst1 T
      (ImportedFactsJobConstructor.Ne T)).
  - intro Huniq. apply ImportedFactsJobConstructor.List_Pairwise_cons_inst1.
    + intros y Hy Hxy.
      have HyR := sprop_to_prop _ _
        (ar_membership_correspondence T y xs (ar_list_to_imported xs)
          (@Lean.eq_refl _ _)) Hy.
      have Hcoq : Logic.eq x y := imported_eq_to_coq_eq x y Hxy.
      subst y.
      exact (ar_neg_mem_contra (x \in xs)
        (ar_and_left_truth _ _ Huniq) (sub_nat_prop_to_truth _ HyR)).
    + exact (ar_uniq_truth_forward T xs
        (ar_and_right_truth _ _ Huniq)).
Defined.

Definition ar_uniq_forward (T : eqType) (xs : seq T) :
    uniq xs -> ImportedFactsJobConstructor.List_Nodup_inst1 T
      (ar_list_to_imported xs) :=
  fun H => ar_uniq_truth_forward T xs (sub_nat_prop_to_truth _ H).

Lemma ar_imported_nodup_backward (T : eqType)
    (xs : ImportedFactsJobConstructor.List_inst1 T) :
  ImportedFactsJobConstructor.List_Nodup_inst1 T xs ->
  StrictlyInhabited (uniq (ar_list_to_rocq xs)).
Proof.
  intro Hnodup. induction Hnodup as [|y ys Hhead Htail IH].
  - exact (strictly_inhabits (Logic.eq_refl true)).
  - destruct IH as [IHuniq]. apply strictly_inhabits.
    apply/andP. split; last exact IHuniq.
    apply/negP. intro Hmem.
    have HmemL := prop_to_sprop _ _
      (ar_membership_correspondence T y (ar_list_to_rocq ys) ys
        (ar_list_target_roundtrip ys)) Hmem.
    have Hneq := Hhead y HmemL.
    exact (interpret_strict Logic.False
      (ar_target_false_to_strict (Hneq (@Lean.eq_refl T y)))).
Qed.

Lemma ar_uniq_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedFactsJobConstructor.List_inst1 T) :
  ArListRel xsR xsL ->
  PropSPropRel (uniq xsR) (ImportedFactsJobConstructor.List_Nodup_inst1 T xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Huniq. exact (ar_nodup_transport _ _ Hxs
      (ar_uniq_forward T xsR Huniq)).
  - intro Hnodup.
    have Hcanonical := ar_nodup_transport _ _
      (sub_imported_eq_sym _ _ Hxs) Hnodup.
    have Hstrict := ar_imported_nodup_backward T
      (ar_list_to_imported xsR) Hcanonical.
    destruct Hstrict as [Huniq]. apply strictly_inhabits.
    rewrite (ar_list_source_roundtrip xsR) in Huniq.
    exact Huniq.
Qed.
