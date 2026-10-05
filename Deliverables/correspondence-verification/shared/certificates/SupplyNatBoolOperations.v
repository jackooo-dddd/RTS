From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSupply ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence SupplyBaseAdapter.

(** Minimal artifact-local Nat/Bool interface needed by Supply. Each proof is
    an instantiation of the accepted canonical Nat relation; operations not
    observed by this source file are deliberately omitted. *)

Definition svc_target_zero : Lean.Nat :=
  ImportedSupply.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedSupply.instOfNatNat Lean.Nat_zero).

Definition svc_target_one : Lean.Nat :=
  ImportedSupply.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedSupply.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition svc_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedSupply.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSupply.instHAdd_inst1 Lean.Nat ImportedSupply.instAddNat) a b.

Definition svc_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedSupply.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSupply.instHSub_inst1 Lean.Nat ImportedSupply.instSubNat) a b.

Definition svc_target_lt (a b : Lean.Nat) : SProp :=
  ImportedSupply.LT_lt_inst1 Lean.Nat ImportedSupply.instLTNat a b.

Definition svc_target_decide_lt (a b : Lean.Nat) : ImportedSupply.Bool :=
  ImportedSupply.Decidable_decide (svc_target_lt a b)
    (ImportedSupply.Nat_decLt a b).

Definition svc_target_false_elim (Q : SProp)
    (H : ImportedSupply.False) : Q := match H return Q with end.

Lemma svc_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedSupply.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  SvcBoolRel b (ImportedSupply.Decidable_decide Q d).
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
  SvcBoolRel (~~ bR) (ImportedSupply.Bool_not bL).
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
    (ImportedSupply.Nat_pred (svc_target_sub a b)).
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
    exact (f_equal ImportedSupply.Nat_pred IH).
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
