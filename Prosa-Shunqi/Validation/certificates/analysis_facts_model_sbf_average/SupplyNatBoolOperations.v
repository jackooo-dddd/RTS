(* Re-bound copy of accepted certificates/analysis_facts_sbf/SupplyNatBoolOperations.v for the analysis/facts/model/sbf/average
   artifact; only the imported module name differs. *)
(* Re-bound copy of accepted .work/experiments/analysis_sbf_pred/certificates/SupplyNatBoolOperations.v for the analysis/facts/SBF artifact;
   only the imported module name differs. *)
(** Artifact-local replay: the only source rewrite is the imported module identity.
    Accepted producer source SHA-256: db563b7aef812eb438fa51b4cc8425a1f6bb8b73d7ea1c1a87192ada5659c5f6.
    Substitution: ImportedSupply -> ImportedFactsSbfAverage.
    This file must be recompiled and audited by Rocq. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSbfAverage ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence SupplyBaseAdapter.

(** Minimal artifact-local Nat/Bool interface needed by Supply. Each proof is
    an instantiation of the accepted canonical Nat relation; operations not
    observed by this source file are deliberately omitted. *)

Definition svc_target_zero : Lean.Nat :=
  ImportedFactsSbfAverage.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedFactsSbfAverage.instOfNatNat Lean.Nat_zero).

Definition svc_target_one : Lean.Nat :=
  ImportedFactsSbfAverage.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedFactsSbfAverage.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition svc_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsSbfAverage.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsSbfAverage.instHAdd_inst1 Lean.Nat ImportedFactsSbfAverage.instAddNat) a b.

Definition svc_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsSbfAverage.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsSbfAverage.instHSub_inst1 Lean.Nat ImportedFactsSbfAverage.instSubNat) a b.

Definition svc_target_lt (a b : Lean.Nat) : SProp :=
  ImportedFactsSbfAverage.LT_lt_inst1 Lean.Nat ImportedFactsSbfAverage.instLTNat a b.

Definition svc_target_decide_lt (a b : Lean.Nat) : ImportedFactsSbfAverage.Bool :=
  ImportedFactsSbfAverage.Decidable_decide (svc_target_lt a b)
    (ImportedFactsSbfAverage.Nat_decLt a b).

Definition svc_target_false_elim (Q : SProp)
    (H : ImportedFactsSbfAverage.False) : Q := match H return Q with end.

Lemma svc_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedFactsSbfAverage.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  SvcBoolRel b (ImportedFactsSbfAverage.Decidable_decide Q d).
Proof.
  intro Hrel. unfold SvcBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (svc_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (svc_target_false_elim _ (svc_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma svc_bool_not_related bR bL :
  SvcBoolRel bR bL ->
  SvcBoolRel (~~ bR) (ImportedFactsSbfAverage.Bool_not bL).
Proof.
  intro Hb. destruct bR, bL; cbn in *;
    try exact (@Lean.eq_refl _ _);
    try exact (svc_false_elim _ (svc_false_ne_true Hb));
    try exact (svc_false_elim _
      (svc_false_ne_true (sub_imported_eq_sym _ _ Hb))).
Qed.

Lemma svc_target_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (svc_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma svc_target_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (svc_target_lt aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Lemma svc_decide_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcBoolRel (ltn aR bR) (svc_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply svc_decide_bool_correspondence.
  exact (svc_target_lt_related aR aL bR bL Ha Hb).
Qed.

Lemma svc_target_sub_succ (a b : Lean.Nat) :
  Logic.eq (svc_target_sub a (Lean.Nat_succ b))
    (ImportedFactsSbfAverage.Nat_pred (svc_target_sub a b)).
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
    exact (f_equal ImportedFactsSbfAverage.Nat_pred IH).
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
Print Assumptions svc_decide_lt_related.
Print Assumptions svc_target_sub_related.
Print Assumptions svc_bool_not_related.
Goal Logic.True.
Proof. idtac "AUDIT_END supply_nat_bool_operations". exact I. Qed.
