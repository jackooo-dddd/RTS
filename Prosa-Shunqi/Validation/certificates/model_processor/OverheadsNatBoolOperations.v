(** GENERATED artifact-local proof replay; not an axiom.
    source certificate SHA-256: db563b7aef812eb438fa51b4cc8425a1f6bb8b73d7ea1c1a87192ada5659c5f6
    imported artifact SHA-256: 9aac90bd80f07a1cd05de01cff0d12a5e2010762df17ea218023c735b13d2d08
    Substitutions: Supply import/adapter identities only.
    Must pass Rocq compilation and Print Assumptions audit. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheads ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence OverheadsBaseAdapter.

(** Minimal artifact-local Nat/Bool interface needed by Overheads. Each proof is
    an instantiation of the accepted canonical Nat relation; operations not
    observed by this source file are deliberately omitted. *)

Definition svc_target_zero : Lean.Nat :=
  ImportedOverheads.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedOverheads.instOfNatNat Lean.Nat_zero).

Definition svc_target_one : Lean.Nat :=
  ImportedOverheads.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedOverheads.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition svc_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedOverheads.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedOverheads.instHAdd_inst1 Lean.Nat ImportedOverheads.instAddNat) a b.

Definition svc_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedOverheads.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedOverheads.instHSub_inst1 Lean.Nat ImportedOverheads.instSubNat) a b.

Lemma svc_target_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (svc_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma svc_target_sub_succ (a b : Lean.Nat) :
  Logic.eq (svc_target_sub a (Lean.Nat_succ b))
    (ImportedOverheads.Nat_pred (svc_target_sub a b)).
Proof. reflexivity. Qed.

Lemma svc_target_zero_sub (b : nat) :
  Logic.eq (svc_target_sub Lean.Nat_zero (sub_nat_to_imported b))
    Lean.Nat_zero.
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rewrite svc_target_sub_succ IH. reflexivity.
Qed.

Lemma svc_target_succ_sub_succ (a b : nat) :
  Logic.eq
    (svc_target_sub (Lean.Nat_succ (sub_nat_to_imported a))
      (Lean.Nat_succ (sub_nat_to_imported b)))
    (svc_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rewrite !svc_target_sub_succ.
    exact (f_equal ImportedOverheads.Nat_pred IH).
Qed.

Lemma svc_target_sub_canonical (a b : nat) :
  Logic.eq
    (svc_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  induction b as [|b IH] in a |- *.
  - destruct a; reflexivity.
  - destruct a as [|a].
    + exact (svc_target_zero_sub b.+1).
    + rewrite svc_target_succ_sub_succ. exact (IH a).
Qed.

Lemma svc_target_sub_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (svc_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (coq_eq_to_imported_eq _ _
      (svc_target_sub_canonical aR bR)))
    (sub_imported_eq_congr2 svc_target_sub _ _ _ _ Ha Hb)).
Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN supply_nat_bool_operations". exact I. Qed.
Print Assumptions svc_target_sub_related.
Goal Logic.True.
Proof. idtac "AUDIT_END supply_nat_bool_operations". exact I. Qed.
