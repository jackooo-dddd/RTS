From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import TaskLimitedPreemptiveSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaArmEdfLimitedPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  LimitedPreemptiveCorrespondence TaskPreemptionParametersCorrespondence.

Module I := ImportedRtaArmEdfLimitedPreemptive.
Module S := TaskLimitedPreemptiveSemanticSource.TaskLimitedPreemptiveSemanticSource.
Module J := prosa.LimitedPreemptiveSemanticSource.LimitedPreemptiveSemanticSource.
Module T := prosa.TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module L := prosa.util.list.ListSemanticSource.

(** Definition certificates for [model/task/preemption/limited_preemptive.v].

    Source side: the extracted byte-identical definition blocks and the
    source-local run-to-completion-threshold instance (helper block); target
    side: the compiled Lean definitions.  Inputs: [TaskCost] pointwise by
    [SubNatRel], task preemption points by the accepted [TppPointsRel], job
    preemption points by the accepted [LpJobPreemptionPointsRel], [job_cost]
    by [SvcJobCostRel], [job_task] by [Lean.eq], arrival sequences by
    [ArArrivalSequenceRel], task sets by [ArListRel].  [last0], [size],
    zero-defaulted [nth], [distances], [nondecreasing_sequence] and the
    job-level limited-preemptive model are closed by the accepted
    [LimitedPreemptiveCorrespondence]/[PreemptionParameterCorrespondence];
    task segments by the accepted [TaskPreemptionParametersCorrespondence]. *)

Lemma tlp_first0_canonical (xs : seq nat) :
  SubNatRel (L.first0 xs) (I.Prosa_Util_List_first0 (svc_nat_list_to_imported xs)).
Proof. destruct xs as [|x xs]; exact (@Lean.eq_refl _ _). Qed.

Lemma tlp_first0_related xsR xsL :
  SvcNatListRel xsR xsL -> SubNatRel (L.first0 xsR) (I.Prosa_Util_List_first0 xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _ (tlp_first0_canonical xsR)
    (sub_imported_eq_congr I.Prosa_Util_List_first0 _ _ Hxs)).
Qed.

Section TaskModel.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable ppR : T.TaskPreemptionPoints Task.
  Variable ppL : I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task dT.
  Hypothesis Hpp : TppPointsRel Task ppR ppL.

  Lemma tlp_limited_preemptions_rtc_threshold_related :
    TppRtctRel Task (@S.limited_preemptions_rtc_threshold Task tcR ppR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_limited_preemptions_rtc_threshold Task dT tcL ppL).
  Proof.
    intro tsk. cbn.
    exact (svc_target_sub_related _ _ _ _ (Htc tsk)
      (svc_target_sub_related _ _ _ _
        (task_last_nonpr_segment_correspondence Task ppR ppL Hpp tsk) (sub_nat_rel_canonical 1))).
  Qed.

  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Let MEM (tsk : Task) := ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts).

  Theorem task_beginning_of_execution_in_preemption_points_correspondence :
    PropSPropRel (@S.task_beginning_of_execution_in_preemption_points Task ppR tsR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_task_beginning_of_execution_in_preemption_points
        Task dT ppL tsL).
  Proof.
    unfold S.task_beginning_of_execution_in_preemption_points.
    cbn [I.Prosa_Model_Task_Preemption_LimitedPreemptive_task_beginning_of_execution_in_preemption_points].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (MEM tsk)|].
    exact (sub_nat_eq_correspondence _ _ _ _ (tlp_first0_related _ _ (Hpp tsk)) (sub_nat_rel_canonical O)).
  Qed.

  Theorem task_end_of_execution_in_preemption_points_correspondence :
    PropSPropRel (@S.task_end_of_execution_in_preemption_points Task tcR ppR tsR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_task_end_of_execution_in_preemption_points
        Task dT tcL ppL tsL).
  Proof.
    unfold S.task_end_of_execution_in_preemption_points.
    cbn [I.Prosa_Model_Task_Preemption_LimitedPreemptive_task_end_of_execution_in_preemption_points].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (MEM tsk)|].
    exact (sub_nat_eq_correspondence _ _ _ _ (lp_last0_related _ _ (Hpp tsk)) (Htc tsk)).
  Qed.

  Theorem nondecreasing_task_preemption_points_correspondence :
    PropSPropRel (@S.nondecreasing_task_preemption_points Task ppR tsR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_nondecreasing_task_preemption_points
        Task dT ppL tsL).
  Proof.
    unfold S.nondecreasing_task_preemption_points.
    cbn [I.Prosa_Model_Task_Preemption_LimitedPreemptive_nondecreasing_task_preemption_points].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (MEM tsk)|].
    exact (lp_nondecreasing_sequence_related _ _ (Hpp tsk)).
  Qed.

  Theorem task_segments_are_nonempty_correspondence :
    PropSPropRel (@S.task_segments_are_nonempty Task ppR tsR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_task_segments_are_nonempty Task dT ppL tsL).
  Proof.
    unfold S.task_segments_are_nonempty.
    cbn [I.Prosa_Model_Task_Preemption_LimitedPreemptive_task_segments_are_nonempty].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    have Hd := pp_distances_related _ _ (Hpp tsk).
    apply ar_imp_correspondence; [exact (MEM tsk)|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hn (lp_length_related _ _ Hd))|].
    exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (lp_nthD_related _ _ _ _ Hd Hn)).
  Qed.

  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jpR : J.JobPreemptionPoints Job.
  Variable jpL : I.Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job dJ.
  Hypothesis Hjp : LpJobPreemptionPointsRel Job jpR jpL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma tlp_task_points_of_job_related (j : Job) :
    SvcNatListRel (@T.task_preemption_points Task ppR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task dT ppL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (sub_imported_eq_trans _ _ _ (Hpp _)
      (sub_imported_eq_congr
        (I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task dT ppL)
        _ _ (Hjt j))).
  Qed.

  Theorem consistent_job_segment_count_correspondence :
    PropSPropRel (@S.consistent_job_segment_count Task ppR Job jtR jpR arrR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_consistent_job_segment_count
        Task dT ppL Job dJ jtL jpL arrL).
  Proof.
    unfold S.consistent_job_segment_count.
    cbn [I.Prosa_Model_Task_Preemption_LimitedPreemptive_consistent_job_segment_count].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (sub_nat_eq_correspondence _ _ _ _ (lp_length_related _ _ (Hjp j))
      (lp_length_related _ _ (tlp_task_points_of_job_related j))).
  Qed.

  Theorem job_respects_segment_lengths_correspondence :
    PropSPropRel (@S.job_respects_segment_lengths Task ppR Job jtR jpR arrR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_job_respects_segment_lengths
        Task dT ppL Job dJ jtL jpL arrL).
  Proof.
    unfold S.job_respects_segment_lengths.
    cbn [I.Prosa_Model_Task_Preemption_LimitedPreemptive_job_respects_segment_lengths].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (lp_nthD_related _ _ _ _ (pp_distances_related _ _ (Hjp j)) Hn)
      (lp_nthD_related _ _ _ _ (pp_distances_related _ _ (tlp_task_points_of_job_related j)) Hn)).
  Qed.

  Theorem valid_fixed_preemption_points_task_model_correspondence :
    PropSPropRel (@S.valid_fixed_preemption_points_task_model Task tcR ppR Job jtR jpR arrR tsR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_task_model
        Task dT tcL ppL Job dJ jtL jpL arrL tsL).
  Proof.
    unfold S.valid_fixed_preemption_points_task_model.
    cbn [I.Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_task_model].
    apply ar_and_correspondence; [exact task_beginning_of_execution_in_preemption_points_correspondence|].
    apply ar_and_correspondence; [exact task_end_of_execution_in_preemption_points_correspondence|].
    apply ar_and_correspondence; [exact nondecreasing_task_preemption_points_correspondence|].
    apply ar_and_correspondence; [exact consistent_job_segment_count_correspondence|].
    apply ar_and_correspondence; [exact job_respects_segment_lengths_correspondence|].
    exact task_segments_are_nonempty_correspondence.
  Qed.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Theorem valid_fixed_preemption_points_model_correspondence :
    PropSPropRel (@S.valid_fixed_preemption_points_model Task tcR ppR Job jtR costR jpR arrR tsR)
      (I.Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_model
        Task dT tcL ppL Job dJ jtL costL jpL arrL tsL).
  Proof.
    unfold S.valid_fixed_preemption_points_model.
    cbn [I.Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_model].
    apply ar_and_correspondence.
    - exact (valid_limited_preemptions_job_model_correspondence Job costR costL Hcost jpR jpL Hjp arrR arrL Harr).
    - exact valid_fixed_preemption_points_task_model_correspondence.
  Qed.
End TaskModel.
