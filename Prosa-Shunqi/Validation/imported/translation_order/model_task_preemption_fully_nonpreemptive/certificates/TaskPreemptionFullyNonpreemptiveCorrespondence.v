From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import TaskPreemptionFullyNonpreemptiveSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskPreemptionFullyNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence.

Module I := ImportedTaskPreemptionFullyNonpreemptive.
Module S := TaskPreemptionFullyNonpreemptiveSemanticSource.TaskPreemptionFullyNonpreemptiveSemanticSource.

(** Definition certificates for [model/task/preemption/fully_nonpreemptive.v].

    Source side: the extracted byte-identical definition block and the
    source-local run-to-completion-threshold instance (helper block); target
    side: the compiled Lean definitions.  Input: [TaskCost] pointwise by
    [SubNatRel].  The task models are related by the accepted
    [TppMaxSegmentRel], the local instance by the accepted [TppRtctRel]. *)

Section Model.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).

  Theorem fully_nonpreemptive_task_model_correspondence :
    TppMaxSegmentRel Task (@S.fully_nonpreemptive_task_model Task tcR)
      (I.Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model Task dT tcL).
  Proof. intro tsk. exact (Htc tsk). Qed.

  Lemma tpfn_fully_nonpreemptive_rtc_threshold_related :
    TppRtctRel Task (@S.fully_nonpreemptive_rtc_threshold Task)
      (I.Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_rtc_threshold Task dT).
  Proof. intro tsk. exact (sub_nat_rel_canonical 1). Qed.
End Model.
