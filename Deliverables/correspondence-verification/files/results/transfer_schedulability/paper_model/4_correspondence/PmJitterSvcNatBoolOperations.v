(* Re-bound copy of the accepted certificates/results_transfer_schedulability_criterion/JitterSvcNatBoolOperations.v for this export:
   ImportedCriterion is this export's ImportedPaperModel (all imported names and instance numbers coincide; checked
   by signature) and references to the other re-bound chain modules point to their Pm copies (the module names in
   the inherited provenance comments below were renamed the same way). No block was dropped. *)
(* Re-bound copy of accepted certificates/model_readiness_jitter/PmJitterSvcNatBoolOperations.v for the analysis/facts/behavior/arrivals
   artifact; only the imported module name differs. *)
(* Re-bound copy of the accepted readiness/basic PmJitterSvcNatBoolOperations.v for the
   jitter projection artifact; only module names differ. *)
(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: Validation/certificates/behavior_service/ServiceNatBoolOperations.v
    source-sha256: 2db3cf9acefae93cc3044bc8fa7e7a44e6b6e0fcb8c15d41cdab7519e8dbb84a
    imported-artifact-sha256: e34025aae0f77959dc58e20663acf5f7abdd5af7df286b3f30e38debcd065838 *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPaperModel ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence PmJitterSvcBaseAdapter.

(** Artifact-local Nat and Bool operations used by the compiled Service
definitions.  These are instances of the already-certified canonical Nat
relation; only the imported operation names are local to this artifact. *)

Definition svc_target_zero : Lean.Nat :=
  ImportedPaperModel.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedPaperModel.instOfNatNat Lean.Nat_zero).

Definition svc_target_one : Lean.Nat :=
  ImportedPaperModel.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedPaperModel.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition svc_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedPaperModel.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedPaperModel.instHAdd_inst1 Lean.Nat ImportedPaperModel.instAddNat) a b.

Definition svc_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedPaperModel.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedPaperModel.instHSub_inst1 Lean.Nat ImportedPaperModel.instSubNat) a b.

Definition svc_target_le (a b : Lean.Nat) : SProp :=
  ImportedPaperModel.LE_le_inst1 Lean.Nat ImportedPaperModel.instLENat a b.

Definition svc_target_lt (a b : Lean.Nat) : SProp :=
  ImportedPaperModel.LT_lt_inst1 Lean.Nat ImportedPaperModel.instLTNat a b.

Definition svc_target_decide_le (a b : Lean.Nat) : ImportedPaperModel.Bool :=
  ImportedPaperModel.Decidable_decide (svc_target_le a b)
    (ImportedPaperModel.Nat_decLe a b).

Definition svc_target_decide_lt (a b : Lean.Nat) : ImportedPaperModel.Bool :=
  ImportedPaperModel.Decidable_decide (svc_target_lt a b)
    (ImportedPaperModel.Nat_decLt a b).

Definition svc_target_decide_eq (a b : Lean.Nat) : ImportedPaperModel.Bool :=
  ImportedPaperModel.Decidable_decide (Lean.eq a b)
    (ImportedPaperModel.instDecidableEqNat a b).

Definition svc_target_false_elim (Q : SProp)
    (H : ImportedPaperModel.False) : Q := match H return Q with end.

Lemma svc_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedPaperModel.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  SvcBoolRel b (ImportedPaperModel.Decidable_decide Q d).
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
  SvcBoolRel (~~ bR) (ImportedPaperModel.Bool_not bL).
Proof.
  intro Hb. destruct bR, bL; cbn in *;
    try exact (@Lean.eq_refl _ _);
    try exact (svc_false_elim _ (svc_false_ne_true Hb));
    try exact (svc_false_elim _
      (svc_false_ne_true (sub_imported_eq_sym _ _ Hb))).
Qed.

Lemma svc_bool_and_related aR aL bR bL :
  SvcBoolRel aR aL -> SvcBoolRel bR bL ->
  SvcBoolRel (aR && bR) (ImportedPaperModel.Bool_and aL bL).
Proof.
  intros Ha Hb. destruct aR, aL, bR, bL; cbn in *;
    try exact (@Lean.eq_refl _ _);
    try exact (svc_false_elim _ (svc_false_ne_true Ha));
    try exact (svc_false_elim _ (svc_false_ne_true Hb));
    try exact (svc_false_elim _
      (svc_false_ne_true (sub_imported_eq_sym _ _ Ha)));
    try exact (svc_false_elim _
      (svc_false_ne_true (sub_imported_eq_sym _ _ Hb))).
Qed.

Lemma svc_target_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (svc_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma svc_target_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (svc_target_le aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.

Lemma svc_target_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (svc_target_lt aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Lemma svc_decide_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcBoolRel (leq aR bR) (svc_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply svc_decide_bool_correspondence.
  exact (svc_target_le_related aR aL bR bL Ha Hb).
Qed.

Lemma svc_decide_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcBoolRel (ltn aR bR) (svc_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply svc_decide_bool_correspondence.
  exact (svc_target_lt_related aR aL bR bL Ha Hb).
Qed.

Lemma svc_decide_eq_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcBoolRel (aR == bR) (svc_target_decide_eq aL bL).
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
    (ImportedPaperModel.Nat_pred (svc_target_sub a b)).
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
    exact (f_equal ImportedPaperModel.Nat_pred IH).
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
Proof. idtac "AUDIT_BEGIN svc_nat_bool_operations". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_END svc_nat_bool_operations". exact I. Qed.
