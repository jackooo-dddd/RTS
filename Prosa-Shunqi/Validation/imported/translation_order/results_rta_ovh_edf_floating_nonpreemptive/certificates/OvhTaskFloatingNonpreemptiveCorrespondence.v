(* Helper copy of the accepted TaskFloatingNonpreemptiveCorrespondence.v of the accepted restricted-supply floating nonpreemptive EDF certificate chain, re-bound to this export and
   to the replayed arrivals modules of this chain; its helper lemma
   tfn_floating_preemptive_rtc_threshold_related is dropped (its target, the task-level run-to-completion
   threshold, is not part of this export and is not used here). *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import TaskFloatingNonpreemptiveSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaOvhEdfFloatingNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence
  OvhLimitedPreemptiveCorrespondence OvhTaskPreemptionParametersCorrespondence.

Module I := ImportedRtaOvhEdfFloatingNonpreemptive.
Module S := TaskFloatingNonpreemptiveSemanticSource.TaskFloatingNonpreemptiveSemanticSource.
Module J := prosa.LimitedPreemptiveSemanticSource.LimitedPreemptiveSemanticSource.
Module T := prosa.TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

(** Definition certificates for [model/task/preemption/floating_nonpreemptive.v].

    Source side: the extracted byte-identical definition blocks (elaborated
    with the job-level limited-preemptive instance enabled by the source's
    [#[local] Existing Instance]) and the source-local run-to-completion
    threshold (helper block); target side: the compiled Lean definitions,
    which pass the accepted Lean [limited_preemptive_job_model] explicitly.
    The two job models are related by the accepted
    [lp_limited_preemptive_job_model_related]; segment lengths and the
    job-level validity by the accepted [OvhPreemptionParameterCorrespondence] and
    [OvhLimitedPreemptiveCorrespondence]; the task bound by the accepted
    [TppMaxSegmentRel]. *)

Section Floating.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).

  Variable mR : T.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jpR : J.JobPreemptionPoints Job.
  Variable jpL : I.Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job dJ.
  Hypothesis Hjp : LpJobPreemptionPointsRel Job jpR jpL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma tfn_limited_model_related :
    PpJobPreemptableRel Job (@J.limited_preemptive_job_model Job jpR)
      (I.Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job dJ jpL).
  Proof.
    intros j nR nL Hn. exact (lp_limited_preemptive_job_model_related Job jpR jpL Hjp j nR nL Hn).
  Qed.

  Theorem job_respects_task_max_np_segment_correspondence :
    PropSPropRel (@S.job_respects_task_max_np_segment Task mR Job jtR costR jpR arrR)
      (I.Prosa_Model_Task_Preemption_FloatingNonpreemptive_job_respects_task_max_np_segment
        Task dT mL Job dJ jtL costL jpL arrL).
  Proof.
    unfold S.job_respects_task_max_np_segment.
    cbn [I.Prosa_Model_Task_Preemption_FloatingNonpreemptive_job_respects_task_max_np_segment].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (job_max_nonpreemptive_segment_correspondence Job costR costL Hcost _ _ tfn_limited_model_related j)
      (sub_imported_eq_trans _ _ _ (Hm _)
        (sub_imported_eq_congr
          (I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment
            Task dT mL) _ _ (Hjt j)))).
  Qed.

  Theorem valid_model_with_floating_nonpreemptive_regions_correspondence :
    PropSPropRel (@S.valid_model_with_floating_nonpreemptive_regions Task mR Job jtR costR jpR arrR)
      (I.Prosa_Model_Task_Preemption_FloatingNonpreemptive_valid_model_with_floating_nonpreemptive_regions
        Task dT mL Job dJ jtL costL jpL arrL).
  Proof.
    unfold S.valid_model_with_floating_nonpreemptive_regions.
    cbn [I.Prosa_Model_Task_Preemption_FloatingNonpreemptive_valid_model_with_floating_nonpreemptive_regions].
    apply ar_and_correspondence.
    - exact (valid_limited_preemptions_job_model_correspondence Job costR costL Hcost jpR jpL Hjp arrR arrL Harr).
    - exact job_respects_task_max_np_segment_correspondence.
  Qed.
End Floating.
