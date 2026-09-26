From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import DemandBoundFunctionSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedDemandBoundFunction ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  RequestBoundFunctionCorrespondence.

Module I := ImportedDemandBoundFunction.
Module S := DemandBoundFunctionSemanticSource.DemandBoundFunctionSemanticSource.

(** Definition certificates for [analysis/definitions/demand_bound_function.v].

    Source side: the extracted byte-identical definition blocks (their
    request-bound-function import bound to the accepted extracted RBF source);
    target side: the compiled Lean declarations.  Inputs: [TaskCost],
    [TaskDeadline] and [MaxArrivals] pointwise by [SubNatRel], task sets by
    [ArListRel].  The RBF and the sequence sum are closed by the accepted
    [RequestBoundFunctionCorrespondence] re-instantiated at this artifact. *)

Section Dbf.
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
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
    SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).

  Theorem task_demand_bound_function_correspondence (tsk : Task) (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.task_demand_bound_function Task tcR tdR maR tsk dR)
      (I.Prosa_Analysis_Definitions_DemandBoundFunction_task_demand_bound_function
        Task dT tcL tdL maL tsk dL).
  Proof.
    intro Hd. unfold S.task_demand_bound_function.
    cbn [I.Prosa_Analysis_Definitions_DemandBoundFunction_task_demand_bound_function].
    exact (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
      (svc_target_sub_related _ _ _ _ Hd
        (svc_target_sub_related _ _ _ _ (Htd tsk) (sub_nat_rel_canonical 1)))).
  Qed.

  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Theorem total_demand_bound_function_correspondence (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.total_demand_bound_function Task tcR tdR maR tsR dR)
      (I.Prosa_Analysis_Definitions_DemandBoundFunction_total_demand_bound_function
        Task dT tcL tdL maL tsL dL).
  Proof.
    intro Hd. unfold S.total_demand_bound_function.
    cbn [I.Prosa_Analysis_Definitions_DemandBoundFunction_total_demand_bound_function].
    exact (rbf_sum_related _ _ _
      (fun tsk => task_demand_bound_function_correspondence tsk dR dL Hd) _ _ Hts).
  Qed.
End Dbf.
