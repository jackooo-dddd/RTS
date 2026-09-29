(* Helper-only copy of the accepted certificates/analysis_abstract_restricted_supply_search_space_edf/SearchSpaceEdfCorrespondence.v (re-bound to this export),
   without its statement correspondence search_space_sub_correspondence (whose target statement is not
   part of this export); every other helper definition and lemma is unchanged. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import SearchSpaceEdfSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaArmEdfLimitedPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence
  WorkloadBoundedCorrespondence EdfAthepBoundCorrespondence TaskPreemptionParametersCorrespondence
  BlockingBoundEdfCorrespondence.

Module I := ImportedRtaArmEdfLimitedPreemptive.
Module S := SearchSpaceEdfSemanticSource.SearchSpaceEdfSemanticSource.

(** Correspondences for [analysis/abstract/restricted_supply/search_space/edf.v].

    Source side: the extracted definition block (with its section-local
    Lets) and the extracted statement [S.statement_search_space_sub]
    specialised at its leading inputs (task type, [task_cost],
    [task_deadline], [task_max_nonpreemptive_segment], the task set and
    [max_arrivals]); target side: the compiled Lean definition and the
    imported Lean theorem type at related inputs ([SubNatRel] on
    [task_cost]/[task_deadline], the accepted [TppMaxSegmentRel],
    [ArListRel], the accepted [CvMaxArrivalsRel]).  Tasks are identity
    carriers and Nats are covered in both directions.  The definition is
    related as Booleans: [has] through kernel-checked Lean [List.any]
    equations exported with the artifact, [!=] through the Lean
    [decide (¬ P) = !decide P] observation.  The abstract search-space
    predicate (pinned source) is related by unfolding both sides, as for the
    accepted FP search space.  RBFs, the EDF blocking bound and the athep
    bound are closed by the accepted certificates re-instantiated at this
    artifact.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma sse_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma sse_nat_neq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (aR <> bR) (I.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb. unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (sub_nat_eq_correspondence aR aL bR bL Ha Hb).
  - exact sse_false_correspondence.
Qed.

Lemma sse_or_correspondence (P Q : Prop) (PL QL : SProp) :
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

Lemma sse_and3_correspondence (b1 b2 : bool) (P : Prop) (Q1 Q2 PL : SProp) :
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

Lemma sse_decide_not (P : SProp) (d : I.Decidable P) :
  Lean.eq (I.Decidable_decide (I.Not P) (I.instDecidableNot P d))
    (I.Bool_not (I.Decidable_decide P d)).
Proof. destruct d; exact (@Lean.eq_refl _ _). Qed.

Lemma sse_nat_neqb_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcBoolRel (aR != bR)
    (I.Decidable_decide (I.Ne Lean.Nat aL bL)
      (I.instDecidableNot (Lean.eq aL bL) (I.instDecidableEqNat aL bL))).
Proof.
  intros Ha Hb. unfold SvcBoolRel.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (sse_decide_not _ _))).
  exact (svc_bool_not_related _ _ (svc_decide_eq_related _ _ _ _ Ha Hb)).
Qed.

Section Any.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

  Lemma sse_has_canonical (xs : seq X) :
    ArBoolRel (has PR xs) (I.List_any X (ar_list_to_imported xs) PL).
  Proof.
    induction xs as [|x xs IH].
    - exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_SearchSpaceEdfInterface_production_any_nil X PL)).
    - cbn [has ar_list_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_SearchSpaceEdfInterface_production_any_cons
          X PL x (ar_list_to_imported xs)))).
      exact (pp_bool_or_related _ _ _ _ (HP x) IH).
  Qed.

  Lemma sse_has_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any X xsL PL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (sse_has_canonical xsR)
      (sub_imported_eq_congr (fun l => I.List_any X l PL) _ _ Hxs)).
  Qed.
End Any.

Section SearchSpace.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
  Variable mR : TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Let RBF tsk := task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk.
  Let BB tsk := blocking_bound_correspondence Task tcR tcL Htc maR maL Hma tdR tdL Htd mR mL Hm
    tsR tsL Hts tsk.
  Let ONE := sub_nat_rel_canonical (S O).

  (** *** The EDF search-space definition *)

  Theorem is_in_search_space_correspondence (tsk : Task) (LR AR : nat) (LL AL : Lean.Nat) :
    SubNatRel LR LL -> SubNatRel AR AL ->
    SvcBoolRel (@S.is_in_search_space Task tcR tdR mR tsR maR tsk LR AR)
      (I.Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Edf_is_in_search_space
        Task dT tcL tdL mL tsL maL tsk LL AL).
  Proof.
    intros HL HA. unfold S.is_in_search_space.
    cbn [I.Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Edf_is_in_search_space].
    refine (ar_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ HA HL) _).
    refine (pp_bool_or_related _ _ _ _ (pp_bool_or_related _ _ _ _ _ _) _).
    - exact (sse_nat_neqb_related _ _ _ _ (BB tsk _ _ (svc_target_sub_related _ _ _ _ HA ONE))
        (BB tsk _ _ HA)).
    - exact (sse_nat_neqb_related _ _ _ _ (RBF tsk _ _ HA)
        (RBF tsk _ _ (svc_target_add_related _ _ _ _ HA ONE))).
    - apply sse_has_related; [|exact Hts]. intro tsko.
      exact (ar_bool_and_related _ _ _ _ (wl_ne_observation Task tsk tsko)
        (sse_nat_neqb_related _ _ _ _
          (RBF tsko _ _ (svc_target_sub_related _ _ _ _
            (svc_target_add_related _ _ _ _ HA (Htd tsk)) (Htd tsko)))
          (RBF tsko _ _ (svc_target_sub_related _ _ _ _
            (svc_target_add_related _ _ _ _ (svc_target_add_related _ _ _ _ HA ONE) (Htd tsk))
            (Htd tsko))))).
  Qed.

  (** *** The statement *)

  Let IBF tsk aR aL (Ha : SubNatRel aR aL) fR fL (Hf : SubNatRel fR fL) :=
    svc_target_add_related _ _ _ _
      (svc_target_sub_related _ _ _ _
        (RBF tsk _ _ (svc_target_add_related _ _ _ _ Ha ONE)) (Htc tsk))
      (svc_target_add_related _ _ _ _ (BB tsk _ _ Ha)
        (bound_on_athep_workload_correspondence Task tcR tcL Htc tdR tdL Htd maR maL Hma tsR tsL Hts
          tsk aR fR aL fL Ha Hf)).
End SearchSpace.
