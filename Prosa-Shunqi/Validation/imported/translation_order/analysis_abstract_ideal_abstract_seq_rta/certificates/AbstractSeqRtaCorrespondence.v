From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import AbstractSeqRtaSemanticSource.
From prosa Require Import analysis.abstract.definitions analysis.abstract.search_space model.job.properties
  model.processor.platform_properties model.task.arrival.curves.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAbstractSeqRta ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence 
  WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter 
  ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses 
  AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations 
  AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical 
  ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations 
  AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers 
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations 
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence 
  TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter 
  ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence 
  RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence 
  IbfTaskFullHelpers.

Module I := ImportedAbstractSeqRta.
Module S := AbstractSeqRtaSemanticSource.AbstractSeqRtaSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module PPC := FoundationCertificates.PreemptionParameterCorrespondence.
Module TPPC := FoundationCertificates.TaskPreemptionParametersCorrespondence.
Module TPP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module RBC := FoundationCertificates.RequestBoundFunctionCorrespondence.
Module SQC := FoundationCertificates.SequentialityCorrespondence.

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** Statement correspondences for [analysis/abstract/ideal/abstract_seq_rta.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types and classes and, for the main
    theorem, the processor state type); target side: the imported Lean
    theorem types.  Inputs: processor states by the accepted two-sided
    [SvcProcessorStateRel] (the preemption-parameter family's relation built
    from it by the accepted [iarta_jsvc]); [task_cost], [task_rtct],
    [job_arrival], [job_cost] pointwise; [JobTask] by [AdJobTaskRel];
    [JobPreemptable] by [PpJobPreemptableRel].  Arrival sequences,
    schedules, task sets, [MaxArrivals], [Interference],
    [InterferingWorkload] and interference-bound functions are covered in
    both directions by the accepted covers.  All definitions are related by
    the accepted definition certificates of the IBF/task, ideal abstract-RTA,
    abstract-RTA, preemption, sequentiality and request-bound-function
    families; [valid_taskset_arrival_curve] is related here pointwise.  No
    source or target theorem is used. *)

Section AbstractSeqRta.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable rtcR : TPP.TaskRunToCompletionThreshold Task.
  Variable rtcL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hrtc : forall tsk : Task,
    SubNatRel (@TPP.task_rtct Task rtcR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task dT rtcL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j) (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j) (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).
  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PPC.PpJobPreemptableRel Job jpR jpL.

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  Lemma asr_valid_taskset_curve_rel tsR tsL (Hts : ArListRel tsR tsL) maR maL
      (Hma : IbtMaxArrivalsRel Task maR maL) :
    PropSPropRel (@prosa.model.task.arrival.curves.valid_taskset_arrival_curve Task tsR
        (@prosa.model.task.arrival.curves.max_arrivals Task maR))
      (I.Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task dT tsL
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL)).
  Proof.
    unfold prosa.model.task.arrival.curves.valid_taskset_arrival_curve.
    cbn [I.Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve].
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    unfold prosa.model.task.arrival.curves.valid_arrival_curve.
    cbn [I.Prosa_Model_Task_Arrival_Curves_valid_arrival_curve].
    apply ad_and_correspondence.
    - exact (sub_nat_eq_correspondence _ _ _ _ (Hma tsk _ _ (sub_nat_rel_canonical O)) (sub_nat_rel_canonical O)).
    - unfold prosa.util.rel.monotone. cbn [I.Prosa_Util_Rel_monotone].
      apply ad_forall_nat_correspondence => xR xL Hx.
      apply ad_forall_nat_correspondence => yR yL Hy.
      imp (ad_bool_truth_correspondence _ _ (svc_decide_le_related _ _ _ _ Hx Hy)).
      exact (ad_bool_truth_correspondence _ _ (svc_decide_le_related _ _ _ _ (Hma tsk _ _ Hx) (Hma tsk _ _ Hy))).
  Qed.

  (** *** max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis *)

  Definition src_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis : Prop :=
    ltac:(body_of (fun s : S.statement_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis =>
      s Task tcR rtcR Job jtR costR jpR)).
  Definition tgt_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_AbstractSeqRta_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis
      Task dT Job dJ tcL rtcL jtL costL jpL)).

  Theorem max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis_correspondence :
    PropSPropRel src_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis
      tgt_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis.
  Proof.
    unfold src_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis,
      tgt_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis.
    apply (iarta_forall_arr Job). intros arrR arrL Harr.
    apply (arta_forall_list Task). intros tsR tsL Hts.
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    apply (ibt_forall_ma Task). intros maR maL Hma.
    imp (asr_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    apply ad_forall_nat_correspondence => LR LL HL.
    apply arta_forall_fun. intros IR IL HI.
    apply ad_forall_nat_correspondence => RR RL HR.
    apply ad_imp_correspondence.
    - apply ad_forall_nat_correspondence => AR AL HA.
      apply ad_imp_correspondence.
      { apply arta_search_space_rel; [|exact HL|exact HA].
        intros xR xL dR dL Hx Hd.
        exact (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _
          (RBC.task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
            (arta_add_related _ _ _ _ Hx (sub_nat_rel_canonical 1))) (Htc tsk)) (HI _ _ _ _ Hx Hd)). }
      apply ad_exists_nat_correspondence => FR FL HF.
      have HAF := arta_add_related _ _ _ _ HA HF.
      apply ad_and_correspondence.
      + exact (sub_nat_le_correspondence _ _ _ _ (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _
          (RBC.task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
            (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1)))
          (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk))) (HI _ _ _ _ HA HAF)) HAF).
      + exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ HF (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk))) HR).
    - imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hma tsk _ _ (sub_nat_rel_canonical 1))).
      apply ad_forall_nat_correspondence => AR AL HA.
      apply ad_imp_correspondence.
      { apply arta_search_space_rel; [|exact HL|exact HA].
        intros xR xL dR dL Hx Hd.
        exact (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _
          (RBC.task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
            (arta_add_related _ _ _ _ Hx (sub_nat_rel_canonical 1))) (Htc tsk)) (HI _ _ _ _ Hx Hd)). }
      apply ad_exists_nat_correspondence => FR FL HF.
      have HAF := arta_add_related _ _ _ _ HA HF.
      apply ad_and_correspondence.
      + exact (sub_nat_le_correspondence _ _ _ _ (arta_add_related _ _ _ _ (Hrtc tsk)
          (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _
            (RBC.task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
              (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1))) (Htc tsk)) (HI _ _ _ _ HA HAF))) HAF).
      + exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ HF (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk))) HR).
  Qed.

  (** *** uniprocessor_response_time_bound_seq *)

  Definition src_uniprocessor_response_time_bound_seq : Prop :=
    ltac:(body_of (fun s : S.statement_uniprocessor_response_time_bound_seq =>
      s Task tcR rtcR Job jtR jaR costR jpR PStateR)).
  Definition tgt_uniprocessor_response_time_bound_seq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_AbstractSeqRta_uniprocessor_response_time_bound_seq
      Task dT Job dJ tcL rtcL jtL jaL costL jpL PStateL)).

  Theorem uniprocessor_response_time_bound_seq_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_seq tgt_uniprocessor_response_time_bound_seq.
  Proof.
    unfold src_uniprocessor_response_time_bound_seq, tgt_uniprocessor_response_time_bound_seq.
    imp (ibt_uni Job PStateR PStateL R).
    imp (iarta_unit_service_rel Job PStateR PStateL R).
    imp (iarta_ideal_progress_rel Job PStateR PStateL R).
    apply (iarta_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (iarta_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    imp (ibt_come_from Job PStateR PStateL R sR sL Hs arrR arrL Harr).
    imp (iarta_must_arrive_rel Job PStateR PStateL R jaR jaL Hja sR sL Hs).
    imp (iarta_completed_dont_execute_rel Job PStateR PStateL R costR costL Hcost sR sL Hs).
    imp (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr).
    apply (arta_forall_list Task). intros tsR tsL Hts.
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL
      (iarta_jsvc Job PStateR PStateL R) sR sL Hs arrR arrL Harr).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    apply (ibt_forall_ma Task). intros maR maL Hma.
    imp (asr_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    imp (ibt_taskset_respects Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply (arta_forall_inter Job). intros iR iL Hi.
    apply (arta_forall_iw Job). intros wR wL Hw.
    imp (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr iR iL Hi wR wL Hw).
    imp (SQC.sequential_tasks_correspondence Job Task jtR jtL Hjt jaR jaL Hja costR costL Hcost PStateR PStateL
      (iarta_jsvc Job PStateR PStateL R) arrR arrL Harr sR sL Hs).
    imp (interference_and_workload_consistent_with_sequential_tasks_correspondence Task Job PStateR PStateL R
      jtR jtL Hjt jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr iR iL Hi wR wL Hw tsk).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (arta_bounded_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
      sR sL Hs arrR arrL Harr iR iL Hi wR wL Hw tsk LR LL HL).
    apply arta_forall_fun. intros IR IL HI.
    imp (task_interference_is_bounded_by_correspondence Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja
      costR costL Hcost sR sL Hs arrR arrL Harr iR iL Hi wR wL Hw tsk IR IL HI).
    apply ad_forall_nat_correspondence => RR RL HR.
    apply ad_imp_correspondence.
    - apply ad_forall_nat_correspondence => AR AL HA.
      apply ad_imp_correspondence.
      + apply arta_search_space_rel; [|exact HL|exact HA].
        intros xR xL dR dL Hx Hd.
        exact (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _
          (RBC.task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
            (arta_add_related _ _ _ _ Hx (sub_nat_rel_canonical 1))) (Htc tsk)) (HI _ _ _ _ Hx Hd)).
      + apply ad_exists_nat_correspondence => FR FL HF.
        have HAF := arta_add_related _ _ _ _ HA HF.
        apply ad_and_correspondence.
        * exact (sub_nat_le_correspondence _ _ _ _ (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _
            (RBC.task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
              (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1)))
            (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk))) (HI _ _ _ _ HA HAF)) HAF).
        * exact (sub_nat_le_correspondence _ _ _ _
            (arta_add_related _ _ _ _ HF (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk))) HR).
    - exact (arta_response_time_bound_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
        sR sL Hs arrR arrL Harr tsk RR RL HR).
  Qed.
End AbstractSeqRta.
