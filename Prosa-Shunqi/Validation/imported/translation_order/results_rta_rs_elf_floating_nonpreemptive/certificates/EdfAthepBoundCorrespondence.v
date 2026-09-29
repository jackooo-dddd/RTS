From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import EdfAthepBoundSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaRsElfFloatingNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  RequestBoundFunctionCorrespondence.

Module I := ImportedRtaRsElfFloatingNonpreemptive.
Module S := EdfAthepBoundSemanticSource.EdfAthepBoundSemanticSource.

(** Definition certificate for [analysis/definitions/workload/edf_athep_bound.v].

    Source side: the extracted byte-identical definition block (its
    request-bound-function import bound to the accepted extracted RBF
    source); target side: the compiled Lean definition.  Inputs: [TaskCost],
    [TaskDeadline] and [MaxArrivals] pointwise by [SubNatRel], task sets by
    [ArListRel], the Nat arguments by [SubNatRel].  The RBF, the filtered
    sequence sum and [!=] are closed by the accepted
    [RequestBoundFunctionCorrespondence] re-instantiated at this artifact;
    [minn] is related to Lean's [min] by kernel-checked Lean case equations
    exported with the artifact.  No source or target theorem is used. *)

Definition eab_target_min (a b : Lean.Nat) : Lean.Nat :=
  ltac:(let T := type of (I.Prosa_Validation_EdfAthepBoundInterface_production_min_of_le a b) in
        match T with _ -> @Lean.eq _ ?L _ => exact L end).

Lemma eab_min_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (minn aR bR) (eab_target_min aL bL).
Proof.
  intros Ha Hb. unfold eab_target_min.
  have Hle := sub_nat_le_correspondence aR aL bR bL Ha Hb.
  have Hge := sub_nat_le_correspondence bR bL aR aL Hb Ha.
  destruct (leq aR bR) eqn:Hab.
  - have Hm : minn aR bR = aR := elimT minn_idPl Hab.
    rewrite Hm.
    exact (sub_imported_eq_trans _ _ _ Ha (sub_imported_eq_sym _ _
      (I.Prosa_Validation_EdfAthepBoundInterface_production_min_of_le _ _
        (prop_to_sprop _ _ Hle isT)))).
  - have Hba : is_true (leq bR aR).
    { apply: ltnW. rewrite ltnNge Hab. done. }
    have Hm : minn aR bR = bR := elimT minn_idPr Hba.
    rewrite Hm.
    exact (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_sym _ _
      (I.Prosa_Validation_EdfAthepBoundInterface_production_min_of_ge _ _
        (prop_to_sprop _ _ Hge Hba)))).
Qed.

Section EdfAthep.
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
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Theorem bound_on_athep_workload_correspondence (tsk : Task) (aR dR : nat) (aL dL : Lean.Nat) :
    SubNatRel aR aL -> SubNatRel dR dL ->
    SubNatRel (@S.bound_on_athep_workload Task tcR tdR maR tsR tsk aR dR)
      (I.Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload
        Task dT tcL tdL maL tsL tsk aL dL).
  Proof.
    intros Ha Hd. unfold S.bound_on_athep_workload.
    cbn [I.Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload].
    apply rbf_sum_filtered_related; [|intro o; exact (rbf_neq_related Task o tsk)|exact Hts].
    intro o.
    exact (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma o _ _
      (eab_min_related _ _ _ _
        (svc_target_sub_related _ _ _ _
          (svc_target_add_related _ _ _ _
            (svc_target_add_related _ _ _ _ Ha (sub_nat_rel_canonical 1)) (Htd tsk))
          (Htd o))
        Hd)).
  Qed.
End EdfAthep.
