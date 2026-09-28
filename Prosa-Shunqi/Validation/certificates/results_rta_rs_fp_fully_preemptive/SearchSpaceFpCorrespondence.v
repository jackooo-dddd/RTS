From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import SearchSpaceFpSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaRsFpFullyPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence
  WorkloadBoundedCorrespondence TaskPreemptionParametersCorrespondence
  BlockingBoundFpCorrespondence.

Module I := ImportedRtaRsFpFullyPreemptive.
Module S := SearchSpaceFpSemanticSource.SearchSpaceFpSemanticSource.

(** Correspondences for [analysis/abstract/restricted_supply/search_space/fp.v].

    Source side: the extracted definition block and the extracted statement
    [S.statement_search_space_sub] specialised at its leading inputs (task
    type, [task_cost], [task_max_nonpreemptive_segment], the FP policy, the
    task set and [max_arrivals]); target side: the compiled Lean definition
    and the imported Lean theorem type at related inputs ([SubNatRel] on
    [task_cost], the accepted [TppMaxSegmentRel], the FP policy pointwise on
    Booleans, [ArListRel], the accepted [CvMaxArrivalsRel]).  Tasks are
    identity carriers and Nats are covered in both directions.  The abstract
    search-space predicate (pinned source) is related to the accepted Lean
    predicate by unfolding both sides: the source's Boolean [0 < A < B] is
    reshaped to the target's nested conjunction, the bounded witness is
    covered by the Nat existential.  RBFs, the total other-hep RBF and the FP
    blocking bound are closed by the accepted certificates re-instantiated
    at this artifact.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma ssfp_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma ssfp_nat_neq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (aR <> bR) (I.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb. unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (sub_nat_eq_correspondence aR aL bR bL Ha Hb).
  - exact ssfp_false_correspondence.
Qed.

Lemma ssfp_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p|q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p|q].
    + exact (strictly_inhabits (or_introl _ (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror _ (sprop_to_prop _ _ HQ q))).
Qed.

Lemma ssfp_and3_correspondence (b1 b2 : bool) (P : Prop) (Q1 Q2 PL : SProp) :
  PropSPropRel (is_true b1) Q1 -> PropSPropRel (is_true b2) Q2 -> PropSPropRel P PL ->
  PropSPropRel (is_true (b1 && b2) /\ P) (Lean.And Q1 (Lean.And Q2 PL)).
Proof.
  intros H1 H2 HP.
  have R := ar_and_correspondence _ _ _ _ H1 (ar_and_correspondence _ _ _ _ H2 HP).
  apply prop_sprop_rel_intro.
  - intros [Hb Hp]. apply (prop_to_sprop _ _ R).
    move/andP: Hb => [h1 h2]. by split; [|split].
  - intro HL. apply strictly_inhabits.
    move: (sprop_to_prop _ _ R HL) => [h1 [h2 hp]].
    split; [apply/andP; split|]; assumption.
Qed.

Lemma ssfp_decide_not (P : SProp) (d : I.Decidable P) :
  Lean.eq (I.Decidable_decide (I.Not P) (I.instDecidableNot P d))
    (I.Bool_not (I.Decidable_decide P d)).
Proof. destruct d; exact (@Lean.eq_refl _ _). Qed.

Lemma ssfp_nat_neqb_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcBoolRel (aR != bR)
    (I.Decidable_decide (I.Ne Lean.Nat aL bL)
      (I.instDecidableNot (Lean.eq aL bL) (I.instDecidableEqNat aL bL))).
Proof.
  intros Ha Hb. unfold SvcBoolRel.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (ssfp_decide_not _ _))).
  exact (svc_bool_not_related _ _ (svc_decide_eq_related _ _ _ _ Ha Hb)).
Qed.

Section SearchSpace.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.

  Let RBF tsk := task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk.

  (** *** The FP search-space definition *)

  Theorem is_in_search_space_correspondence (tsk : Task) (LR AR : nat) (LL AL : Lean.Nat) :
    SubNatRel LR LL -> SubNatRel AR AL ->
    SvcBoolRel (@S.is_in_search_space Task tcR maR tsk LR AR)
      (I.Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fp_is_in_search_space
        Task dT tcL maL tsk LL AL).
  Proof.
    intros HL HA. unfold S.is_in_search_space.
    cbn [I.Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fp_is_in_search_space].
    exact (ar_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ HA HL)
      (ssfp_nat_neqb_related _ _ _ _ (RBF tsk _ _ HA)
        (RBF tsk _ _ (svc_target_add_related _ _ _ _ HA (sub_nat_rel_canonical (S O)))))).
  Qed.

  (** *** The statement *)

  Variable mR : TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : forall x y : Task,
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Let IBF tsk aR aL (Ha : SubNatRel aR aL) fR fL (Hf : SubNatRel fR fL) :=
    svc_target_add_related _ _ _ _
      (svc_target_sub_related _ _ _ _
        (RBF tsk _ _ (svc_target_add_related _ _ _ _ Ha (sub_nat_rel_canonical (S O)))) (Htc tsk))
      (svc_target_add_related _ _ _ _
        (blocking_bound_correspondence Task mR mL Hm fpR fpL Hfp tsR tsL Hts tsk)
        (total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma
          tsR tsL Hts fpR fpL Hfp tsk fR fL Hf)).

  Definition src_search_space_sub : Prop :=
    ltac:(body_of (fun s : S.statement_search_space_sub => s Task tcR mR fpR tsR maR)).
  Definition tgt_search_space_sub : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fp_search_space_sub
      Task dT tcL mL fpL tsL maL)).
  Theorem search_space_sub_correspondence : PropSPropRel src_search_space_sub tgt_search_space_sub.
  Proof.
    apply ar_imp_correspondence;
      [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply ar_forall_nat_correspondence. intros LR LL HL.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL)|].
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk))|].
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
        (Hma tsk (S O) _ (sub_nat_rel_canonical (S O))))|].
    apply ar_forall_nat_correspondence. intros AR AL HA.
    apply ar_imp_correspondence.
    - unfold prosa.analysis.abstract.search_space.is_in_search_space,
        prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than.
      cbn [I.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
        I.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than].
      apply ssfp_or_correspondence;
        [exact (sub_nat_eq_correspondence _ _ _ _ HA (sub_nat_rel_canonical O))|].
      apply ssfp_and3_correspondence.
      + exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HA).
      + exact (sub_nat_lt_correspondence _ _ _ _ HA HL).
      + apply ar_exists_nat_correspondence. intros xR xL Hx.
        apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hx HL)|].
        have HA1 := svc_target_sub_related _ _ _ _ HA (sub_nat_rel_canonical (S O)).
        exact (ssfp_nat_neq_correspondence _ _ _ _ (IBF tsk _ _ HA1 _ _ Hx) (IBF tsk _ _ HA _ _ Hx)).
    - exact (ar_bool_truth_correspondence _ _ (is_in_search_space_correspondence tsk _ _ _ _ HL HA)).
  Qed.
End SearchSpace.
