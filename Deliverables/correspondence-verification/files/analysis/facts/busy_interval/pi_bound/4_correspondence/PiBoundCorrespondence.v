From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import PiBoundSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.job.properties analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPiBound ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers
  TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers.

Module I := ImportedPiBound.
Module S := PiBoundSemanticSource.PiBoundSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PPS := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PIS := PriorityInversionSemanticSource.PriorityInversionSemanticSource.

(** Statement correspondence for [analysis/facts/busy_interval/pi_bound.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, the task-level maximum nonpreemptive segment, the
    job-task, arrival, cost and preemptability classes, the arrival
    sequence); target side: the imported Lean theorem type.  Inputs:
    [job_arrival] by [ArJobArrivalRel], [job_cost] by the accepted
    [SvcJobCostRel], [job_task] by [Lean.eq], [TaskMaxNonpreemptiveSegment] by
    the accepted [TppMaxSegmentRel], [JobPreemptable] by the accepted
    [PpJobPreemptableRel], arrival sequences by [ArArrivalSequenceRel].
    Inputs quantified inside the statement are covered in both directions by
    the accepted conversions: processor models, schedules, JLFP policies, the
    readiness instance on the statement's schedule pair, blocking-bound
    functions (pointwise on related Nats, the accepted [ex_forall_fun]),
    tasks and jobs (identity) and instants.  The task-level bound on priority
    inversion is related by unfolding over the accepted
    busy-interval-existence helper for the job-level bound; the maximum
    lower-priority nonpreemptive segment is the accepted [pi] definition
    certificate; the bounded-nonpreemptive-segment model is the accepted
    task-preemption-parameters certificate.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section PiBound.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Variable mR : TPS.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jpR : PPS.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Definition src_priority_inversion_is_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_priority_inversion_is_bounded =>
      s Task mR Job jtR jaR costR jpR arrR)).
  Definition tgt_priority_inversion_is_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_PiBound_priority_inversion_is_bounded
      Job dJ Task dT mL jtL jaL costL jpL arrL)).

  Theorem priority_inversion_is_bounded_correspondence :
    PropSPropRel src_priority_inversion_is_bounded tgt_priority_inversion_is_bounded.
  Proof.
    unfold src_priority_inversion_is_bounded, tgt_priority_inversion_is_bounded.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (isj_cover_pstate Job). intros PR PL X.
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply fpre_forall_jlfp. intros pR pL Hp.
    imp (hap_transitive_rel Job pR pL Hp).
    imp (ar_and_correspondence _ _ _ _
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp)
      (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL Hcost
        mR mL Hm jpR jpL Hjp arrR arrL Harr)).
    apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs). intros jrR jrL Hjr.
    imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp jrR jrL Hjr).
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr
      jrR jrL Hjr jpR jpL Hjp pR pL Hp).
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp).
    apply ar_forall_identity_correspondence. intro tsk.
    apply ex_forall_fun. intros BR BL HB.
    imp (isj_psr_uniprocessor_related Job PR PL X).
    imp (ex_unit_service_related Job PR PL X).
    imp (isj_psr_ideal_progress_related Job PR PL X).
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      imp (ar_bool_truth_correspondence _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)).
      imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
        arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2).
      exact (sub_nat_le_correspondence _ _ _ _
        (max_lp_nonpreemptive_segment_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp
          jpR jpL Hjp j _ _ Ht1)
        (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1))). }
    unfold PIS.priority_inversion_is_bounded_by.
    cbn [I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by].
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
    exact (ex_pi_bounded_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
      pR pL Hp j BR BL HB).
  Qed.
End PiBound.
