From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsRtcLimitedSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsRtcLimited ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  LimitedPreemptiveCorrespondence ScheduleLimitedPreemptiveCorrespondence
  TaskPreemptionParametersCorrespondence TaskLimitedPreemptiveCorrespondence.

Module I := ImportedFactsRtcLimited.
Module S := FactsRtcLimitedSemanticSource.FactsRtcLimitedSemanticSource.
Module LP := LimitedPreemptiveSemanticSource.LimitedPreemptiveSemanticSource.
Module TP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma rtc_lean_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

(** Statement correspondences for [analysis/facts/preemption/rtc_threshold/limited.v].

    Source side: the extracted statements specialised at their leading inputs
    (task and job types, task cost and preemption points, job-task, job cost
    and preemption points, arrival sequence and, for the second statement,
    processor model and schedule); target side: the imported Lean theorem
    types.  Inputs: [task_cost], [job_cost] pointwise by [SubNatRel],
    [job_task] by [Lean.eq], task preemption points by the accepted
    [TppPointsRel], job preemption points by the accepted
    [LpJobPreemptionPointsRel], arrival sequences by [ArArrivalSequenceRel],
    processor states by [SvcProcessorStateRel], schedules by
    [SvcScheduleRel]; task sets (covered), tasks identity.  The section-local
    [limited_preemptive_job_model] and [limited_preemptions_rtc_threshold]
    are related by the accepted [lp_limited_preemptive_job_model_related] and
    [tlp_limited_preemptions_rtc_threshold_related]; the valid fixed-points
    model, the schedule's respect of the preemption model, the valid
    run-to-completion threshold, list length and the last task segment by the
    accepted definition certificates.  No source or target theorem is used. *)

Lemma frl_forall_list (T : Type) (PRl : seq T -> Prop) (PLl : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PRl xsR) (PLl xsL)) ->
  PropSPropRel (forall xs, PRl xs) (forall xs, PLl xs).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xsL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xsL)) (HR (ar_list_to_rocq xsL))).
  - intro HL. apply strictly_inhabits. intro xs.
    exact (sprop_to_prop _ _ (H _ _ (@Lean.eq_refl _ _)) (HL (ar_list_to_imported xs))).
Qed.

Section RtcLimited.
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
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Variable tppR : TP.TaskPreemptionPoints Task.
  Variable tppL : I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task dT.
  Hypothesis Htpp : TppPointsRel Task tppR tppL.
  Variable jppR : LP.JobPreemptionPoints Job.
  Variable jppL : I.Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job dJ.
  Hypothesis Hjpp : LpJobPreemptionPointsRel Job jppR jppL.

  Let Hjp : PpJobPreemptableRel Job (@LP.limited_preemptive_job_model Job jppR)
      (I.Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job dJ jppL) :=
    fun j nR nL Hn => lp_limited_preemptive_job_model_related Job jppR jppL Hjpp j nR nL Hn.
  Let Hr := tlp_limited_preemptions_rtc_threshold_related Task tcR tcL Htc tppR tppL Htpp.

  Definition src_number_of_preemption_points_in_task_at_least_two : Prop :=
    ltac:(body_of (fun s : S.statement_number_of_preemption_points_in_task_at_least_two =>
      s Task tcR tppR Job jtR costR jppR arrR)).
  Definition tgt_number_of_preemption_points_in_task_at_least_two : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_Limited_number_of_preemption_points_in_task_at_least_two
      Job dJ Task dT tcL tppL jtL costL jppL arrL)).

  Theorem number_of_preemption_points_in_task_at_least_two_correspondence :
    PropSPropRel src_number_of_preemption_points_in_task_at_least_two
      tgt_number_of_preemption_points_in_task_at_least_two.
  Proof.
    unfold src_number_of_preemption_points_in_task_at_least_two,
      tgt_number_of_preemption_points_in_task_at_least_two.
    apply frl_forall_list => tsR tsL Hts.
    imp (valid_fixed_preemption_points_model_correspondence Task tcR tcL Htc tppR tppL Htpp tsR tsL Hts
      Job jtR jtL Hjt jppR jppL Hjpp arrR arrL Harr costR costL Hcost).
    apply ar_forall_identity_correspondence => tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (lp_length_related _ _ (Htpp tsk))).
  Qed.

  Definition src_last_segment_eq_cost_minus_rtct : Prop :=
    ltac:(body_of (fun s : S.statement_last_segment_eq_cost_minus_rtct =>
      s Task tcR tppR Job jtR costR jppR arrR)).
  Definition tgt_last_segment_eq_cost_minus_rtct : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_Limited_last_segment_eq_cost_minus_rtct
      Job dJ Task dT tcL tppL jtL costL jppL arrL)).

  Theorem last_segment_eq_cost_minus_rtct_correspondence :
    PropSPropRel src_last_segment_eq_cost_minus_rtct tgt_last_segment_eq_cost_minus_rtct.
  Proof.
    unfold src_last_segment_eq_cost_minus_rtct, tgt_last_segment_eq_cost_minus_rtct.
    apply frl_forall_list => tsR tsL Hts.
    imp (valid_fixed_preemption_points_model_correspondence Task tcR tcL Htc tppR tppL Htpp tsR tsL Hts
      Job jtR jtL Hjt jppR jppL Hjpp arrR arrL Harr costR costL Hcost).
    apply ar_forall_identity_correspondence => tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    exact (sub_nat_eq_correspondence _ _ _ _ (svc_target_sub_related _ _ _ _ (Htc tsk) (Hr tsk))
      (svc_target_sub_related _ _ _ _ (task_last_nonpr_segment_correspondence Task tppR tppL Htpp tsk)
        (sub_nat_rel_canonical 1))).
  Qed.

  Section Sched.
    Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
    Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable R : SvcProcessorStateRel Job PStateR PStateL.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Definition src_limited_valid_task_run_to_completion_threshold : Prop :=
      ltac:(body_of (fun s : S.statement_limited_valid_task_run_to_completion_threshold =>
        s Task tcR tppR Job jtR costR jppR arrR PStateR schedR)).
    Definition tgt_limited_valid_task_run_to_completion_threshold : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_Limited_limited_valid_task_run_to_completion_threshold
        Job dJ Task dT tcL tppL jtL costL jppL arrL PStateL schedL)).

    Theorem limited_valid_task_run_to_completion_threshold_correspondence :
      PropSPropRel src_limited_valid_task_run_to_completion_threshold
        tgt_limited_valid_task_run_to_completion_threshold.
    Proof.
      unfold src_limited_valid_task_run_to_completion_threshold,
        tgt_limited_valid_task_run_to_completion_threshold.
      imp (schedule_respects_preemption_model_correspondence Job _ _ Hjp PStateR PStateL R
        schedR schedL Hsched arrR arrL Harr).
      apply frl_forall_list => tsR tsL Hts.
      imp (valid_fixed_preemption_points_model_correspondence Task tcR tcL Htc tppR tppL Htpp tsR tsL Hts
        Job jtR jtL Hjt jppR jppL Hjpp arrR arrL Harr costR costL Hcost).
      apply ar_forall_identity_correspondence => tsk.
      imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
      imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
      exact (valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc _ _ Hr
        jtR jtL Hjt costR costL Hcost _ _ Hjp arrR arrL Harr tsk).
    Qed.
  End Sched.
End RtcLimited.
