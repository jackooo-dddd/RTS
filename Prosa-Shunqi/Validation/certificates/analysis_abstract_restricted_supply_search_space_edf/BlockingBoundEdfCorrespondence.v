From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import BlockingBoundEdfSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpaceEdf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence.

Module I := ImportedSearchSpaceEdf.
Module S := BlockingBoundEdfSemanticSource.BlockingBoundEdfSemanticSource.
Module T := prosa.TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

(** Definition certificates for [analysis/definitions/blocking_bound/edf.v].

    Source side: the extracted byte-identical definition blocks; target side:
    the compiled Lean declarations.  Inputs: [TaskCost], [TaskDeadline] and
    [MaxArrivals] pointwise by [SubNatRel], [TaskMaxNonpreemptiveSegment] by
    the accepted [TppMaxSegmentRel], task sets by [ArListRel].  MathComp's
    conditional [\max] big operator is related to [bigMaxListCond] through
    kernel-checked Lean constructor equations exported with the artifact and
    the accepted [maxn]/[Nat.max] correspondence. *)

(** ** Conditional maximum over a sequence *)

Section BigMax.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).
  Variable FR : X -> nat.
  Variable FL : X -> Lean.Nat.
  Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

  Lemma bbe_bigmax_canonical (xs : seq X) :
    SubNatRel (\max_(x <- xs | PR x) FR x)
      (I.Prosa_Util_Minmax_bigMaxListCond X (ar_list_to_imported xs) PL FL).
  Proof.
    induction xs as [|x xs IH].
    - rewrite big_nil.
      exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_nil X PL FL)).
    - rewrite big_cons. cbn [ar_list_to_imported].
      have Hx := HP x. unfold ArBoolRel in Hx.
      destruct (PR x).
      + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_cons_true
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
        refine (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _ (pp_max_canonical (FR x) (\max_(y <- xs | PR y) FR y))) _).
        exact (sub_imported_eq_congr2 I.Nat_max _ _ _ _ (HF x) IH).
      + refine (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
          (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_cons_false
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
  Qed.

  Lemma bbe_bigmax_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL ->
    SubNatRel (\max_(x <- xsR | PR x) FR x) (I.Prosa_Util_Minmax_bigMaxListCond X xsL PL FL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (bbe_bigmax_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Minmax_bigMaxListCond X l PL FL) _ _ Hxs)).
  Qed.
End BigMax.

(** ** Definitions *)

Section Blocking.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
    SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).

  Theorem blocking_relevant_correspondence (tsk : Task) :
    ArBoolRel (@S.blocking_relevant Task tcR maR tsk)
      (I.Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant Task dT tcL maL tsk).
  Proof.
    unfold S.blocking_relevant.
    cbn [I.Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant].
    apply ar_bool_and_related.
    - exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O)
        (Hma tsk _ _ (sub_nat_rel_canonical 1))).
    - exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
  Qed.

  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
  Variable mR : T.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Theorem blocking_bound_correspondence (tsk : Task) (AR : nat) (AL : Lean.Nat) :
    SubNatRel AR AL ->
    SubNatRel (@S.blocking_bound Task tcR tdR mR tsR maR tsk AR)
      (I.Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound
        Task dT tcL tdL mL tsL maL tsk AL).
  Proof.
    intro HA. unfold S.blocking_bound.
    cbn [I.Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound].
    apply bbe_bigmax_related; [| |exact Hts].
    - intro tsk_o. apply ar_bool_and_related.
      + exact (blocking_relevant_correspondence tsk_o).
      + exact (ar_decide_lt_related _ _ _ _
          (svc_target_add_related _ _ _ _ (Htd tsk) HA) (Htd tsk_o)).
    - intro tsk_o.
      exact (svc_target_sub_related _ _ _ _ (Hm tsk_o) (sub_nat_rel_canonical 1)).
  Qed.
End Blocking.
