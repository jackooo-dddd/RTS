From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsTaskLimitedSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsTaskLimited ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  LimitedPreemptiveCorrespondence ScheduleLimitedPreemptiveCorrespondence
  TaskPreemptionParametersCorrespondence TaskLimitedPreemptiveCorrespondence.

Module I := ImportedFactsTaskLimited.
Module S := FactsTaskLimitedSemanticSource.FactsTaskLimitedSemanticSource.
Module LP := LimitedPreemptiveSemanticSource.LimitedPreemptiveSemanticSource.
Module TP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** Statement correspondences for [analysis/facts/preemption/task/limited.v].

    Source side: the extracted statements specialised at their leading inputs
    (task and job types, task cost, job-task, job cost, job and task
    preemption points, arrival sequence, task set or processor model and
    schedule); target side: the imported Lean theorem types.  Inputs:
    [task_cost], [job_cost] pointwise by [SubNatRel], [job_task] by
    [Lean.eq], job preemption points by the accepted
    [LpJobPreemptionPointsRel], task preemption points by the accepted
    [TppPointsRel], arrival sequences by [ArArrivalSequenceRel], task sets
    by [ArListRel] (covered where quantified inside), processor states by the
    accepted two-sided [SvcProcessorStateRel] and schedules by
    [SvcScheduleRel].  The section-local [limited_preemptive_job_model] is
    related by the accepted [lp_limited_preemptive_job_model_related]; the
    task-level maximum nonpreemptive segment (the global conversion from task
    preemption points) by the accepted conversion certificate; the valid
    fixed-preemption-points model, the schedule's respect of the preemption
    model and the bounded-nonpreemptive-segment models by the accepted
    definition certificates.  No source or target theorem is used. *)

Lemma ftl_forall_list (T : Type) (PRl : seq T -> Prop) (PLl : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PRl xsR) (PLl xsL)) ->
  PropSPropRel (forall xs, PRl xs) (forall xs, PLl xs).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xsL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xsL)) (HR (ar_list_to_rocq xsL))).
  - intro HL. apply strictly_inhabits. intro xs.
    exact (sprop_to_prop _ _ (H _ _ (@Lean.eq_refl _ _)) (HL (ar_list_to_imported xs))).
Qed.

Section TaskLimited.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jppR : LP.JobPreemptionPoints Job.
  Variable jppL : I.Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job dJ.
  Hypothesis Hjpp : LpJobPreemptionPointsRel Job jppR jppL.
  Variable tppR : TP.TaskPreemptionPoints Task.
  Variable tppL : I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task dT.
  Hypothesis Htpp : TppPointsRel Task tppR tppL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let Hjp : PpJobPreemptableRel Job (@LP.limited_preemptive_job_model Job jppR)
      (I.Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job dJ jppL) :=
    fun j nR nL Hn => lp_limited_preemptive_job_model_related Job jppR jppL Hjpp j nR nL Hn.
  Let Hm := TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion_correspondence Task tppR tppL Htpp.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Definition src_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions : Prop :=
    ltac:(body_of (fun s : S.statement_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions =>
      s Task tcR Job jtR costR jppR tppR arrR)).
  Definition tgt_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Task_Limited_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
        Job dJ Task dT tcL jtL costL jppL tppL arrL)).

  Theorem fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions_correspondence :
    PropSPropRel src_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
      tgt_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions.
  Proof.
    unfold src_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions,
      tgt_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions.
    apply ftl_forall_list => tsR tsL Hts.
    imp (valid_fixed_preemption_points_model_correspondence Task tcR tcL Htc tppR tppL Htpp tsR tsL Hts
      Job jtR jtL Hjt jppR jppL Hjpp arrR arrL Harr costR costL Hcost).
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

    Definition src_fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions : Prop :=
      ltac:(body_of (fun s : S.statement_fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions =>
        s Task tcR Job jtR costR jppR tppR arrR PStateR schedR)).
    Definition tgt_fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Preemption_Task_Limited_fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
          Job dJ Task dT tcL jtL costL jppL tppL arrL PStateL schedL)).

    Theorem fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence :
      PropSPropRel src_fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
        tgt_fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions.
    Proof.
      unfold src_fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions,
        tgt_fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions.
      imp (schedule_respects_preemption_model_correspondence Job _ _ Hjp PStateR PStateL R
        schedR schedL Hsched arrR arrL Harr).
      apply ftl_forall_list => tsR tsL Hts.
      imp (valid_fixed_preemption_points_model_correspondence Task tcR tcL Htc tppR tppL Htpp tsR tsL Hts
        Job jtR jtL Hjt jppR jppL Hjpp arrR arrL Harr costR costL Hcost).
      exact (valid_model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
        Hcost _ _ Hm _ _ Hjp arrR arrL Harr PStateR PStateL R schedR schedL Hsched).
    Qed.
  End Sched.
End TaskLimited.
