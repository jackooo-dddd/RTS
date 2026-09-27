From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IwAuxiliarySemanticSource analysis.abstract.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIwAuxiliary ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter
  ServiceNatBoolOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical.

Module I := ImportedIwAuxiliary.
Module S := IwAuxiliarySemanticSource.IwAuxiliarySemanticSource.

(** Statement correspondences for [analysis/abstract/iw_auxiliary.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (the job type, the [Interference] instance and the
    Boolean predicates); target side: the imported Lean theorem types (the
    filtered interval sum of [cumul_cond_interference_alt] is exported in the
    accepted list-fold form, under the kernel [rfl] normalization guard of the
    export root).  Inputs: [Interference] by the accepted [AdInterferenceRel],
    the predicates by the accepted [AdBoolPredRel], jobs identity, instants by
    [SubNatRel].  [cumul_cond_interference] and [cumulative_interference] are
    related by the accepted abstract-definitions certificates; the filtered
    source sum is rewritten to its conditional body with mathcomp's
    [big_mkcond] and related by the accepted interval-sum certificate.  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma iwa_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma iwa_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. exact (prop_to_sprop _ _ HQ (H (sprop_to_prop _ _ HP p))).
  - intro H. apply strictly_inhabits. intro p.
    exact (sprop_to_prop _ _ HQ (H (prop_to_sprop _ _ HP p))).
Qed.

Lemma iwa_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [H1 H2]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (H1 (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (H2 (sprop_to_prop _ _ HQ q))).
  - intros [H1 H2]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (H1 (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (H2 (prop_to_sprop _ _ HQ q))).
Qed.

Section IwAuxiliary.
  Context (Job : eqType).
  Let dJ := ad_decidable_eq Job.
  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
  Hypothesis Hinter : AdInterferenceRel Job interR interL.

  Let CUMUL predR predL (Hpred : AdBoolPredRel Job predR predL) :=
    cumul_cond_interference_correspondence Job interR interL Hinter predR predL Hpred.

  Lemma iwa_pred_at predR predL (Hpred : AdBoolPredRel Job predR predL) (j : Job)
      (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    AdBoolRel (predR j tR) (predL j tL).
  Proof. destruct Ht. exact (Hpred j tR). Qed.

  Lemma iwa_true_pred : AdBoolPredRel Job (fun _ _ => true) (fun _ _ => I.Bool_true).
  Proof. intros j t. exact (@Lean.eq_refl _ _). Qed.

  (** *** fold_cumul_interference *)

  Definition src_fold_cumul_interference : Prop :=
    ltac:(body_of (fun s : S.statement_fold_cumul_interference => s Job interR)).
  Definition tgt_fold_cumul_interference : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_IwAuxiliary_fold_cumul_interference Job dJ interL)).

  Theorem fold_cumul_interference_correspondence :
    PropSPropRel src_fold_cumul_interference tgt_fold_cumul_interference.
  Proof.
    unfold src_fold_cumul_interference, tgt_fold_cumul_interference.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
    exact (sub_nat_eq_correspondence _ _ _ _
      (CUMUL _ _ iwa_true_pred j t1R t2R t1L t2L Ht1 Ht2)
      (cumulative_interference_correspondence Job interR interL j t1R t2R t1L t2L Hinter Ht1 Ht2)).
  Qed.

  Section Pred.
    Variable PR : Job -> nat -> bool.
    Variable PL : Job -> Lean.Nat -> I.Bool.
    Hypothesis HP : AdBoolPredRel Job PR PL.

    (** *** cumul_cond_interference_alt *)

    Definition src_cumul_cond_interference_alt : Prop :=
      ltac:(body_of (fun s : S.statement_cumul_cond_interference_alt => s Job interR PR)).
    Definition tgt_cumul_cond_interference_alt : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_IwAuxiliary_cumul_cond_interference_alt
        Job dJ interL PL)).

    Lemma iwa_filtered_sum_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (\sum_(t1R <= t < t2R | PR j t)
          @prosa.analysis.abstract.definitions.interference Job interR j t)
        (svc_target_interval_value t1L t2L
          (fun t => I.cond Lean.Nat (PL j t)
            (I.Bool_toNat (I.Prosa_Analysis_Abstract_Definitions_Interference_interference Job dJ interL j t))
            (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)))).
    Proof.
      intros Ht1 Ht2. rewrite big_mkcond.
      apply svc_interval_sum_related; [exact Ht1 | exact Ht2 |].
      intros nR nL Hn. destruct Hn.
      refine (iwa_lean_transport (fun b => SubNatRel
        (if PR j nR then nat_of_bool (@prosa.analysis.abstract.definitions.interference Job interR j nR) else O)
        (I.cond Lean.Nat b
          (I.Bool_toNat (I.Prosa_Analysis_Abstract_Definitions_Interference_interference Job dJ interL j
            (sub_nat_to_imported nR)))
          (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)))) _ _ (HP j nR) _).
      destruct (PR j nR).
      - exact (ad_bool_to_nat_related _ _ (Hinter j nR)).
      - exact (sub_nat_rel_canonical O).
    Qed.

    Theorem cumul_cond_interference_alt_correspondence :
      PropSPropRel src_cumul_cond_interference_alt tgt_cumul_cond_interference_alt.
    Proof.
      unfold src_cumul_cond_interference_alt, tgt_cumul_cond_interference_alt.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
      exact (sub_nat_eq_correspondence _ _ _ _
        (CUMUL _ _ HP j t1R t2R t1L t2L Ht1 Ht2) (iwa_filtered_sum_related j _ _ _ _ Ht1 Ht2)).
    Qed.

    (** *** cumulative_interference_sub *)

    Definition src_cumulative_interference_sub : Prop :=
      ltac:(body_of (fun s : S.statement_cumulative_interference_sub => s Job interR PR)).
    Definition tgt_cumulative_interference_sub : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_IwAuxiliary_cumulative_interference_sub
        Job dJ interL PL)).

    Theorem cumulative_interference_sub_correspondence :
      PropSPropRel src_cumulative_interference_sub tgt_cumulative_interference_sub.
    Proof.
      unfold src_cumulative_interference_sub, tgt_cumulative_interference_sub.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros alR alL Hal.
      apply ad_forall_nat_correspondence. intros arR arL Har.
      apply ad_forall_nat_correspondence. intros blR blL Hbl.
      apply ad_forall_nat_correspondence. intros brR brL Hbr.
      apply iwa_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hbl Hal)|].
      apply iwa_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Har Hbr)|].
      exact (sub_nat_le_correspondence _ _ _ _
        (CUMUL _ _ HP j _ _ _ _ Hal Har) (CUMUL _ _ HP j _ _ _ _ Hbl Hbr)).
    Qed.

    (** *** cumulative_interference_cat *)

    Definition src_cumulative_interference_cat : Prop :=
      ltac:(body_of (fun s : S.statement_cumulative_interference_cat => s Job interR PR)).
    Definition tgt_cumulative_interference_cat : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_IwAuxiliary_cumulative_interference_cat
        Job dJ interL PL)).

    Theorem cumulative_interference_cat_correspondence :
      PropSPropRel src_cumulative_interference_cat tgt_cumulative_interference_cat.
    Proof.
      unfold src_cumulative_interference_cat, tgt_cumulative_interference_cat.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
      apply iwa_imp_correspondence.
      - exact (ad_bool_truth_correspondence _ _ (ad_bool_and_related _ _ _ _
          (svc_decide_le_related _ _ _ _ Ht1 Ht) (svc_decide_le_related _ _ _ _ Ht Ht2))).
      - exact (sub_nat_eq_correspondence _ _ _ _ (CUMUL _ _ HP j _ _ _ _ Ht1 Ht2)
          (sub_add_correspondence _ _ _ _ (CUMUL _ _ HP j _ _ _ _ Ht1 Ht) (CUMUL _ _ HP j _ _ _ _ Ht Ht2))).
    Qed.
  End Pred.

  Section TwoPreds.
    Variable P1R P2R : Job -> nat -> bool.
    Variable P1L P2L : Job -> Lean.Nat -> I.Bool.
    Hypothesis HP1 : AdBoolPredRel Job P1R P1L.
    Hypothesis HP2 : AdBoolPredRel Job P2R P2L.

    (** *** cumul_cond_interference_ID *)

    Definition src_cumul_cond_interference_ID : Prop :=
      ltac:(body_of (fun s : S.statement_cumul_cond_interference_ID => s Job interR P1R P2R)).
    Definition tgt_cumul_cond_interference_ID : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_IwAuxiliary_cumul_cond_interference_ID
        Job dJ interL P1L P2L)).

    Lemma iwa_and_pred : AdBoolPredRel Job (fun j t => P1R j t && P2R j t)
      (fun j t => I.Bool_and (P1L j t) (P2L j t)).
    Proof. intros j t. exact (ad_bool_and_related _ _ _ _ (HP1 j t) (HP2 j t)). Qed.

    Lemma iwa_and_not_pred : AdBoolPredRel Job (fun j t => P1R j t && ~~ P2R j t)
      (fun j t => I.Bool_and (P1L j t) (I.Bool_not (P2L j t))).
    Proof.
      intros j t. exact (ad_bool_and_related _ _ _ _ (HP1 j t) (svc_bool_not_related _ _ (HP2 j t))).
    Qed.

    Theorem cumul_cond_interference_ID_correspondence :
      PropSPropRel src_cumul_cond_interference_ID tgt_cumul_cond_interference_ID.
    Proof.
      unfold src_cumul_cond_interference_ID, tgt_cumul_cond_interference_ID.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
      exact (sub_nat_eq_correspondence _ _ _ _ (CUMUL _ _ HP1 j _ _ _ _ Ht1 Ht2)
        (sub_add_correspondence _ _ _ _ (CUMUL _ _ iwa_and_pred j _ _ _ _ Ht1 Ht2)
          (CUMUL _ _ iwa_and_not_pred j _ _ _ _ Ht1 Ht2))).
    Qed.

    (** *** cumul_cond_interference_pred_eq *)

    Definition src_cumul_cond_interference_pred_eq : Prop :=
      ltac:(body_of (fun s : S.statement_cumul_cond_interference_pred_eq => s Job interR P1R P2R)).
    Definition tgt_cumul_cond_interference_pred_eq : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_IwAuxiliary_cumul_cond_interference_pred_eq
        Job dJ interL P1L P2L)).

    Theorem cumul_cond_interference_pred_eq_correspondence :
      PropSPropRel src_cumul_cond_interference_pred_eq tgt_cumul_cond_interference_pred_eq.
    Proof.
      unfold src_cumul_cond_interference_pred_eq, tgt_cumul_cond_interference_pred_eq.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
      apply iwa_imp_correspondence.
      - apply ad_forall_identity_correspondence. intro j0.
        apply ad_forall_nat_correspondence. intros tR tL Ht.
        exact (iwa_iff_correspondence _ _ _ _
          (ad_bool_truth_correspondence _ _ (iwa_pred_at _ _ HP1 j0 tR tL Ht))
          (ad_bool_truth_correspondence _ _ (iwa_pred_at _ _ HP2 j0 tR tL Ht))).
      - exact (sub_nat_eq_correspondence _ _ _ _ (CUMUL _ _ HP1 j _ _ _ _ Ht1 Ht2)
          (CUMUL _ _ HP2 j _ _ _ _ Ht1 Ht2)).
    Qed.
  End TwoPreds.
End IwAuxiliary.
