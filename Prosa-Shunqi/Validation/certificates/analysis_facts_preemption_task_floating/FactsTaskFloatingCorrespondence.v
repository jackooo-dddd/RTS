From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsTaskFloatingSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsTaskFloating ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  LimitedPreemptiveCorrespondence ScheduleLimitedPreemptiveCorrespondence
  TaskPreemptionParametersCorrespondence TaskFloatingNonpreemptiveCorrespondence.

Module I := ImportedFactsTaskFloating.
Module S := FactsTaskFloatingSemanticSource.FactsTaskFloatingSemanticSource.
Module LP := LimitedPreemptiveSemanticSource.LimitedPreemptiveSemanticSource.
Module TP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** Statement correspondences for [analysis/facts/preemption/task/floating.v].

    Source side: the extracted statements specialised at their leading inputs
    (task and job types, job-task, job cost, task maximum nonpreemptive
    segment, job preemption points, arrival sequence and, for the second
    statement, the processor model and schedule); target side: the imported
    Lean theorem types.  Inputs: [job_cost] by the accepted [SvcJobCostRel],
    [job_task] by [Lean.eq], the task maximum nonpreemptive segment by the
    accepted [TppMaxSegmentRel], job preemption points by the accepted
    [LpJobPreemptionPointsRel], arrival sequences by [ArArrivalSequenceRel],
    processor states by the accepted two-sided [SvcProcessorStateRel] and
    schedules by [SvcScheduleRel].  The section-local
    [limited_preemptive_job_model] is related by the accepted
    [lp_limited_preemptive_job_model_related]; the floating model, the
    schedule's respect of the preemption model and the
    bounded-nonpreemptive-segment models by the accepted definition
    certificates.  No source or target theorem is used. *)

Section TaskFloating.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable mR : TP.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable jppR : LP.JobPreemptionPoints Job.
  Variable jppL : I.Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job dJ.
  Hypothesis Hjpp : LpJobPreemptionPointsRel Job jppR jppL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let Hjp : PpJobPreemptableRel Job (@LP.limited_preemptive_job_model Job jppR)
      (I.Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job dJ jppL) :=
    fun j nR nL Hn => lp_limited_preemptive_job_model_related Job jppR jppL Hjpp j nR nL Hn.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Definition src_floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions : Prop :=
    ltac:(body_of (fun s : S.statement_floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions =>
      s Task Job jtR costR mR jppR arrR)).
  Definition tgt_floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Task_Floating_floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
        Job dJ Task dT jtL costL mL jppL arrL)).

  Theorem floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions_correspondence :
    PropSPropRel src_floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
      tgt_floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions.
  Proof.
    unfold src_floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions,
      tgt_floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions.
    imp (valid_model_with_floating_nonpreemptive_regions_correspondence Task mR mL Hm Job jtR jtL Hjt
      costR costL Hcost jppR jppL Hjpp arrR arrL Harr).
    exact (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL Hcost
      _ _ Hm _ _ Hjp arrR arrL Harr).
  Qed.

  Section Sched.
    Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
    Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable R : SvcProcessorStateRel Job PStateR PStateL.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Definition src_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions : Prop :=
      ltac:(body_of (fun s : S.statement_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions =>
        s Task Job jtR costR mR jppR arrR PStateR schedR)).
    Definition tgt_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Preemption_Task_Floating_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
          Job dJ Task dT jtL costL mL jppL arrL PStateL schedL)).

    Theorem floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence :
      PropSPropRel src_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
        tgt_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions.
    Proof.
      unfold src_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions,
        tgt_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions.
      imp (schedule_respects_preemption_model_correspondence Job _ _ Hjp PStateR PStateL R
        schedR schedL Hsched arrR arrL Harr).
      imp (valid_model_with_floating_nonpreemptive_regions_correspondence Task mR mL Hm Job jtR jtL Hjt
        costR costL Hcost jppR jppL Hjpp arrR arrL Harr).
      exact (valid_model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
        Hcost _ _ Hm _ _ Hjp arrR arrL Harr PStateR PStateL R schedR schedL Hsched).
    Qed.
  End Sched.
End TaskFloating.
