From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsPreemptiveTaskSemanticSource.
From prosa Require Import model.preemption.fully_preemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPreemptiveTask ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence TaskPreemptionFullyPreemptiveCorrespondence.

Module I := ImportedFactsPreemptiveTask.
Module S := FactsPreemptiveTaskSemanticSource.FactsPreemptiveTaskSemanticSource.

(** Statement correspondences for [analysis/facts/preemption/task/preemptive.v].

    Source side: the extracted statements [S.statement_X] (elaborated with
    the source's section-local fully preemptive job and task instances)
    specialised at their leading inputs; target side: the imported Lean
    theorem types, which pass the accepted Lean [fully_preemptive_job_model]
    and [fully_preemptive_task_model] explicitly.  The source job instance
    (compiled from the pinned [fully_preemptive.v]) is related to the Lean
    definition as a [PpJobPreemptableRel]; the task instance by the accepted
    [fully_preemptive_task_model_correspondence].  Inputs: [job_task] by
    [Lean.eq], [job_cost] by [SvcJobCostRel], processor states and schedules
    by the accepted two-sided [SvcProcessorStateRel]/[SvcScheduleRel],
    arrival sequences by [ArArrivalSequenceRel].  The bounded-segment
    predicates are closed by the accepted
    [TaskPreemptionParametersCorrespondence].  No source or target theorem
    is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section Preemptive.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Lemma fptp_fully_preemptive_job_related :
    PpJobPreemptableRel Job
      (@prosa.model.preemption.fully_preemptive.fully_preemptive_job_model Job)
      (I.Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job dJ).
  Proof. intros j nR nL Hn. exact (@Lean.eq_refl _ _). Qed.

  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Definition src_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions : Prop :=
    ltac:(body_of (fun s : S.statement_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions =>
      s Task Job jtR costR arrR)).
  Definition tgt_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Task_Preemptive_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions
        Task dT Job dJ jtL costL arrL)).
  Theorem fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence :
    PropSPropRel src_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions
      tgt_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions.
  Proof.
    exact (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt
      costR costL Hcost _ _ (fully_preemptive_task_model_correspondence Task)
      _ _ fptp_fully_preemptive_job_related arrR arrL Harr).
  Qed.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Definition src_fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments : Prop :=
    ltac:(body_of (fun s : S.statement_fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments =>
      s Task Job jtR costR PStateR arrR schedR)).
  Definition tgt_fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Task_Preemptive_fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments
        Task dT Job dJ jtL costL PStateL arrL schedL)).
  Theorem fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments_correspondence :
    PropSPropRel src_fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments
      tgt_fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments.
  Proof.
    exact (valid_model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt
      costR costL Hcost _ _ (fully_preemptive_task_model_correspondence Task)
      _ _ fptp_fully_preemptive_job_related arrR arrL Harr PStateR PStateL R schedR schedL Hsched).
  Qed.
End Preemptive.
