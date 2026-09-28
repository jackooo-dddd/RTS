From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FifoAhepBoundSemanticSource.
From prosa Require Import model.job.properties model.processor.platform_properties model.processor.supply
  model.priority.fifo.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFifoAhepBound ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers IdealAbstractRtaHelpers.
From FoundationCertificates Require
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence SequentialityCorrespondence
  IbfTaskHelpers IbfSupplyTaskCorrespondence ServiceInversionPredCorrespondence
  InterferenceCorrespondence ServiceOfJobsCorrespondence CurvesCorrespondence
  RequestBoundFunctionCorrespondence
  WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence.
From FoundationCertificates Require Import IbfTaskFullHelpers RsIwHelpers.

Module I := ImportedFifoAhepBound.
Module S := FifoAhepBoundSemanticSource.FifoAhepBoundSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module CV := FoundationCertificates.CurvesCorrespondence.
Module RBF := FoundationCertificates.RequestBoundFunctionCorrespondence.
Module IFC := FoundationCertificates.InterferenceCorrespondence.

(** Statement correspondence for [analysis/facts/priority/fifo_ahep_bound.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, [task_cost], [max_arrivals], [job_task],
    [job_cost], [job_arrival], a leading processor state); target side: the
    imported Lean theorem type.  Inputs: [task_cost], [job_cost] and
    [job_arrival] pointwise; [max_arrivals] by the accepted
    [CvMaxArrivalsRel]; [job_task] by the accepted [AdJobTaskRel]; the
    processor state by the accepted two-sided [SvcProcessorStateRel] together
    with the pointwise [supply_on] relation (the accepted restricted-supply
    family relations).  Arrival sequences, schedules, task sets, tasks, jobs
    (identity) and instants are covered in both directions.  The FIFO policy
    is related pointwise from the arrival input; classical busy intervals are
    the accepted restricted-supply helper relation; the cumulative
    interference of other higher-or-equal-priority jobs and the task RBFs are
    the accepted definition certificates re-instantiated at this artifact.
    No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section FifoAhepBound.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Hypothesis Hsupply_on : forall sR sL cR,
    SSO.svc_ps_state_rel Job PStateR PStateL R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (SUP.supply_target_supply_on Job PStateL sL (SSO.svc_ps_core_to_target Job PStateR PStateL R cR)).
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CV.CvMaxArrivalsRel Task maR maL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  Let FR := @prosa.model.priority.fifo.FIFO Job jaR.
  Let FL := I.Prosa_Model_Priority_Fifo_FIFO Job dJ jaL.

  Lemma fah_fifo_rel : RsiJLFPRel Job FR FL.
  Proof. intros x y. exact (svc_decide_le_related _ _ _ _ (Hja x) (Hja y)). Qed.

  Lemma fah_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (arta_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma fah_valid_job_costs_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (fah_task_cost_of_job_related j))).
  Qed.

  Lemma fah_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
      tsR tsL (Hts : ArListRel tsR tsL) :
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _ (arta_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j \in tsR)
        (ar_target_decide_mem Task v tsL)) _ _ (Hjt j)
      (ar_decide_mem_related Task (@prosa.model.task.concept.job_task Job Task jtR j) _ _ Hts))).
  Qed.

  Definition src_bound_on_hep_workload : Prop :=
    ltac:(body_of (fun s : S.statement_bound_on_hep_workload =>
      s Task tcR maR Job jtR costR jaR PStateR)).
  Definition tgt_bound_on_hep_workload : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Priority_FifoAhepBound_bound_on_hep_workload
        Task dT tcL maL Job dJ jtL costL jaL PStateL)).

  Theorem bound_on_hep_workload_correspondence :
    PropSPropRel src_bound_on_hep_workload tgt_bound_on_hep_workload.
  Proof.
    unfold src_bound_on_hep_workload, tgt_bound_on_hep_workload.
    imp (ibt_uni Job PStateR PStateL R).
    imp (rsi_unit_supply_rel Job PStateR PStateL R Hsupply_on).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    imp (fah_valid_job_costs_rel arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (fah_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (CV.taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
      maR maL Hma).
    imp (CV.valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma).
    apply ad_forall_identity_correspondence. intro tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    imp (rsi_must_arrive_rel Job PStateR PStateL R jaR jaL Hja sR sL Hs).
    imp (rsi_completed_dont_execute_rel Job PStateR PStateL R costR costL Hcost sR sL Hs).
    apply ad_forall_identity_correspondence. intro j.
    imp (ar_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt)).
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))).
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    imp (rsi_busy_interval_related Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs
      arrR arrL Harr FR FL fah_fifo_rel j _ _ _ _ H1 H2).
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have H1d := svc_target_add_related _ _ _ _ H1 Hd.
    imp (sub_nat_lt_correspondence _ _ _ _ H1d H2).
    exact (sub_nat_le_correspondence _ _ _ _
      (IFC.cumulative_another_hep_job_interference_correspondence Job PStateR PStateL
        (rsi_jsvc Job PStateR PStateL R) sR sL (rsi_hs_jsvc Job PStateR PStateL R sR sL Hs)
        arrR arrL Harr FR FL fah_fifo_rel j _ _ _ _ H1 H1d)
      (svc_target_sub_related _ _ _ _
        (RBF.rbf_sum_related _ _ _
          (fun tsko => RBF.task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsko _ _
            (svc_target_add_related _ _ _ _ (svc_target_sub_related _ _ _ _ (Hja j) H1)
              (sub_nat_rel_canonical (S O))))
          _ _ Hts)
        (Htc tsk))).
  Qed.
End FifoAhepBound.
