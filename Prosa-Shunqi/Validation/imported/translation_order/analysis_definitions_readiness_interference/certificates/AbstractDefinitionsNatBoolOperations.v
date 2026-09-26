(* Re-bound copy of accepted imported/translation_order/abstract_definitions/certificates/AbstractDefinitionsNatBoolOperations.v for the readiness_interference artifact;
   only the imported module name differs. *)
(** GENERATED proof replay, not an axiom.
    accepted source SHA-256: db563b7aef812eb438fa51b4cc8425a1f6bb8b73d7ea1c1a87192ada5659c5f6
    imported artifact SHA-256: 57a6dceff588a42239e89321523942914c3c20f4ced1f44ef7d90ca14640940b. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessInterference ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence AbstractDefinitionsBaseAdapter.

(** Minimal artifact-local Nat/Bool interface needed by Supply. Each proof is
    an instantiation of the accepted canonical Nat relation; operations not
    observed by this source file are deliberately omitted. *)

Definition svc_target_zero : Lean.Nat :=
  ImportedReadinessInterference.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedReadinessInterference.instOfNatNat Lean.Nat_zero).

Definition svc_target_one : Lean.Nat :=
  ImportedReadinessInterference.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedReadinessInterference.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition svc_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedReadinessInterference.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedReadinessInterference.instHAdd_inst1 Lean.Nat ImportedReadinessInterference.instAddNat) a b.

Definition svc_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedReadinessInterference.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedReadinessInterference.instHSub_inst1 Lean.Nat ImportedReadinessInterference.instSubNat) a b.

Definition svc_target_lt (a b : Lean.Nat) : SProp :=
  ImportedReadinessInterference.LT_lt_inst1 Lean.Nat ImportedReadinessInterference.instLTNat a b.

Definition svc_target_decide_lt (a b : Lean.Nat) : ImportedReadinessInterference.Bool :=
  ImportedReadinessInterference.Decidable_decide (svc_target_lt a b)
    (ImportedReadinessInterference.Nat_decLt a b).

Definition ad_target_decide_nat_eq (a b : Lean.Nat) : ImportedReadinessInterference.Bool :=
  ImportedReadinessInterference.Decidable_decide (Lean.eq a b)
    (ImportedReadinessInterference.instDecidableEqNat a b).

Definition svc_target_false_elim (Q : SProp)
    (H : ImportedReadinessInterference.False) : Q := match H return Q with end.

Lemma svc_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedReadinessInterference.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  AdBoolRel b (ImportedReadinessInterference.Decidable_decide Q d).
Proof.
  intro Hrel. unfold AdBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (svc_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (svc_target_false_elim _ (ad_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma svc_bool_not_related bR bL :
  AdBoolRel bR bL ->
  AdBoolRel (~~ bR) (ImportedReadinessInterference.Bool_not bL).
Proof.
  intro Hb. destruct bR, bL; cbn in *;
    try exact (@Lean.eq_refl _ _);
    try exact (ad_false_elim _ (ad_false_ne_true Hb));
    try exact (ad_false_elim _
      (ad_false_ne_true (sub_imported_eq_sym _ _ Hb))).
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
  AdBoolRel (ltn aR bR) (svc_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply svc_decide_bool_correspondence.
  exact (svc_target_lt_related aR aL bR bL Ha Hb).
Qed.

Lemma ad_decide_nat_eq_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  AdBoolRel (aR == bR) (ad_target_decide_nat_eq aL bL).
Proof.
  intros Ha Hb. apply svc_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intro Heq. apply (prop_to_sprop _ _
      (sub_nat_eq_correspondence aR aL bR bL Ha Hb)).
    by move/eqP: Heq.
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence aR aL bR bL Ha Hb) Heq).
Qed.

Lemma svc_target_sub_succ (a b : Lean.Nat) :
  Logic.eq (svc_target_sub a (Lean.Nat_succ b))
    (ImportedReadinessInterference.Nat_pred (svc_target_sub a b)).
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
    exact (f_equal ImportedReadinessInterference.Nat_pred IH).
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
Print Assumptions ad_decide_nat_eq_related.
Print Assumptions svc_target_sub_related.
Print Assumptions svc_bool_not_related.
Goal Logic.True.
Proof. idtac "AUDIT_END supply_nat_bool_operations". exact I. Qed.
