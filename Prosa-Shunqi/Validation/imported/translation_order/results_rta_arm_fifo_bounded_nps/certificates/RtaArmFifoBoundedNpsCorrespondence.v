From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import RtaArmFifoBoundedNpsSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply analysis.definitions.sbf.pred
  model.readiness.basic model.priority.fifo model.schedule.work_conserving
  model.composite.valid_task_arrival_sequence analysis.definitions.sbf.average.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaArmFifoBoundedNps ImportedSubadditivity.
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
  TaskPreemptionParametersCorrespondence SequentialityCorrespondence CurvesCorrespondence
  RequestBoundFunctionCorrespondence
  IbfTaskHelpers IbfSupplyTaskCorrespondence ServiceInversionPredCorrespondence
  InterferenceCorrespondence ServiceOfJobsCorrespondence
  WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence
  ArrivalSequenceCorrespondence BusyIntervalClassicalHelpers PredHelpers SbfBusyCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence
  SearchSpaceFifoCorrespondence.
From FoundationCertificates Require Import PcoBaseAdapter.
From FoundationCertificates Require Import IbfTaskFullHelpers RsIwHelpers RsPStateCover.
From FoundationCertificates Require AverageCorrespondence.

Module I := ImportedRtaArmFifoBoundedNps.
Module S := RtaArmFifoBoundedNpsSemanticSource.RtaArmFifoBoundedNpsSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module JSI := FoundationCertificates.JitterSvcIntervalOperations.
Module CV := FoundationCertificates.CurvesCorrespondence.
Module RBF := FoundationCertificates.RequestBoundFunctionCorrespondence.
Module PC := FoundationCertificates.PredHelpers.
Module SBFB := FoundationCertificates.SbfBusyCorrespondence.

Module PPC := FoundationCertificates.PreemptionParameterCorrespondence.
Module TPPC := FoundationCertificates.TaskPreemptionParametersCorrespondence.
Module PTC := FoundationCertificates.PreemptionTimeCorrespondence.
Module JSO := FoundationCertificates.JitterSvcScheduleOperations.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module PPS := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

Module SSF := FoundationCertificates.SearchSpaceFifoCorrespondence.
Module AVG := FoundationCertificates.AverageCorrespondence.
Module SCH := SchedulabilitySemanticSource.SchedulabilitySemanticSource.

(** Correspondences for [results/rta/arm/fifo/bounded_nps.v].

    Derived from the accepted restricted-supply certificate of the same policy and preemption model,
    with the resource-model delta of the accepted ARM FP fully preemptive certificate.  The processor
    model is quantified inside the statement and covered in both directions by [rs_forall_pstate]
    (the accepted two-sided [SvcProcessorStateRel] with the pointwise [supply_on] relation).
    Readiness is the basic readiness model, related at each related schedule pair from the accepted
    pending relation.
    [valid_task_arrival_sequence] unfolds into the accepted arrival-sequence, job-cost, task-set and
    arrival-curve relations; the average resource model and [arm_sbf] are the accepted certificates over the
    supply view of the processor relation, replacing the supply bound function.  All other relations
    are those of the restricted-supply certificate.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Covers *)

Definition rfp_fun1_to_target (fR : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun xL => sub_nat_to_imported (fR (sub_nat_to_rocq xL)).
Definition rfp_fun1_to_source (fL : Lean.Nat -> Lean.Nat) : nat -> nat :=
  fun xR => sub_nat_to_rocq (fL (sub_nat_to_imported xR)).

Lemma rfp_fun1_to_target_rel fR : JSI.SvcNatFunRel fR (rfp_fun1_to_target fR).
Proof.
  intros xR xL Hx. unfold rfp_fun1_to_target.
  rewrite (arta_nat_input _ _ Hx). exact (sub_nat_rel_canonical _).
Qed.

Lemma rfp_fun1_to_source_rel fL : JSI.SvcNatFunRel (rfp_fun1_to_source fL) fL.
Proof. intros xR xL Hx. destruct Hx. exact (sub_nat_imported_roundtrip _). Qed.

Lemma rfp_forall_fun1 (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, JSI.SvcNatFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  exact (arta_forall_cover _ _ JSI.SvcNatFunRel rfp_fun1_to_target rfp_fun1_to_source
    rfp_fun1_to_target_rel rfp_fun1_to_source_rel PR PL).
Qed.

Definition RfpSbfRel (sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction)
    (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) : SProp :=
  PC.PredFunctionRel sR (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL).

Definition rfp_sbf_to_target (fR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction) :
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction :=
  I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
    (fun dL => sub_nat_to_imported (fR (sub_nat_to_rocq dL))).
Definition rfp_sbf_to_source (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :
    prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction :=
  ((fun dR => sub_nat_to_rocq
    (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL (sub_nat_to_imported dR)))
    : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction).

Lemma rfp_forall_sbf (PR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction -> Prop)
    (PL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> SProp) :
  (forall sR sL, RfpSbfRel sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  apply (arta_forall_cover _ _ RfpSbfRel rfp_sbf_to_target rfp_sbf_to_source).
  - intros fR nR nL Hn. unfold RfpSbfRel, rfp_sbf_to_target. cbn.
    rewrite (arta_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
  - intros sL nR nL Hn. destruct Hn. exact (sub_nat_imported_roundtrip _).
Qed.

Section RtaArmFifoBoundedNps.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CV.CvMaxArrivalsRel Task maR maL.
  Variable rR : TPS.TaskRunToCompletionThreshold Task.
  Variable rL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hr : TPPC.TppRtctRel Task rR rL.
  Variable jpR : PPS.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PPC.PpJobPreemptableRel Job jpR jpL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  (** *** Task-set level predicates *)

  Lemma rfp_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (arta_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma rfp_valid_job_costs_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (rfp_task_cost_of_job_related j))).
  Qed.

  Lemma rfp_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
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


  (** *** Section-local models *)


  Let FR := @prosa.model.priority.fifo.FIFO Job jaR.
  Let FL := I.Prosa_Model_Priority_Fifo_FIFO Job dJ jaL.

  Lemma rff_fifo_rel : RsiJLFPRel Job FR FL.
  Proof. intros x y. exact (svc_decide_le_related _ _ _ _ (Hja x) (Hja y)). Qed.


  Lemma rfa_valid_task_arrival_sequence_rel tsR tsL (Hts : ArListRel tsR tsL)
      arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel
      (@prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence
        Task tcR maR Job jtR costR jaR tsR arrR)
      (I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence
        Task dT tcL maL Job dJ jtL costL jaL tsL arrL).
  Proof.
    unfold prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence.
    cbn [I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence].
    apply ar_and_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_and_correspondence; [exact (rfp_valid_job_costs_rel arrR arrL Harr)|].
    apply ar_and_correspondence; [exact (rfp_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts)|].
    apply ar_and_correspondence.
    - exact (CV.taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
        maR maL Hma).
    - exact (CV.valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma).
  Qed.

  (** *** Schedule-level relations at a related processor-model pair *)

  Section PState.
    Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
    Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.

    Let J := rsi_jsvc Job PStateR PStateL R.
    Let HsJ sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) :=
      rsi_hs_jsvc Job PStateR PStateL R sR sL Hs.

    Lemma rfe_basic_ready_at sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) :
      RsiJrAt Job PStateR PStateL jaR jaL costR costL sR sL
        (@prosa.model.readiness.basic.basic_ready_instance Job PStateR jaR costR)
        (I.Prosa_Model_Readiness_Basic_basic_ready_instance Job dJ PStateL jaL costL).
    Proof.
      intros j tR tL Ht. cbn.
      exact (ibt_pending Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs j tR tL Ht).
    Qed.

    Lemma rfe_respects_jlfp_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL)
        arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
        qpR qpL (Hqp : PPC.PpJobPreemptableRel Job qpR qpL)
        jrR jrL (Hjr : RsiJrAt Job PStateR PStateL jaR jaL costR costL sR sL jrR jrL)
        pR pL (Hp : RsiJLFPRel Job pR pL) :
      PropSPropRel (@PDS.respects_JLFP_policy_at_preemption_point Job jaR costR PStateR qpR jrR arrR sR pR)
        (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
          Job dJ jaL costL PStateL qpL jrL arrL sL pL).
    Proof.
      unfold PDS.respects_JLFP_policy_at_preemption_point, PDS.respects_JLDP_policy_at_preemption_point.
      cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
        I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_identity_correspondence. intro j_hp.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      imp (ar_bool_truth_correspondence _ _
        (PTC.preemption_time_correspondence Job qpR qpL Hqp PStateR PStateL J sR sL (HsJ sR sL Hs)
          arrR arrL Harr tR tL Ht)).
      imp (ar_bool_truth_correspondence _ _
        (rsi_backlogged_related Job PStateR PStateL R jaR jaL costR costL sR sL Hs jrR jrL Hjr j tR tL Ht)).
      imp (ar_bool_truth_correspondence _ _
        (PPC.pp_scheduled_at_related Job PStateR PStateL J sR sL (HsJ sR sL Hs) j_hp tR tL Ht)).
      exact (ar_bool_truth_correspondence _ _ (Hp j_hp j)).
    Qed.
  End PState.

  (** *** The two definitions *)

  Let ONE := sub_nat_rel_canonical (S O).
  Let ARM PiR PiL (HPi : SubNatRel PiR PiL) ThR ThL (HTh : SubNatRel ThR ThL) nuR nuL (Hnu : SubNatRel nuR nuL)
      dR dL (Hd : SubNatRel dR dL) :=
    AVG.arm_sbf_correspondence PiR ThR nuR dR PiL ThL nuL dL HPi HTh Hnu Hd.

  Theorem busy_window_recurrence_solution_correspondence tsR tsL (Hts : ArListRel tsR tsL)
      PiR PiL (HPi : SubNatRel PiR PiL) ThR ThL (HTh : SubNatRel ThR ThL) nuR nuL (Hnu : SubNatRel nuR nuL) (LR : nat) (LL : Lean.Nat) (HL : SubNatRel LR LL) :
    PropSPropRel (@S.busy_window_recurrence_solution Task tcR maR tsR PiR ThR nuR LR)
      (I.Prosa_Results_Rta_Arm_Fifo_BoundedNps_busy_window_recurrence_solution
        Task dT tcL maL tsL PiL ThL nuL LL).
  Proof.
    unfold S.busy_window_recurrence_solution.
    cbn [I.Prosa_Results_Rta_Arm_Fifo_BoundedNps_busy_window_recurrence_solution].
    apply ar_and_correspondence.
    - exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    - exact (sub_nat_le_correspondence _ _ _ _
        (RBF.total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)
        (ARM _ _ HPi _ _ HTh _ _ Hnu _ _ HL)).
  Qed.

  Theorem rta_recurrence_solution_correspondence tsR tsL (Hts : ArListRel tsR tsL)
      PiR PiL (HPi : SubNatRel PiR PiL) ThR ThL (HTh : SubNatRel ThR ThL) nuR nuL (Hnu : SubNatRel nuR nuL)
      (LR : nat) (LL : Lean.Nat) (HL : SubNatRel LR LL) (RR : nat) (RL : Lean.Nat) (HR : SubNatRel RR RL) :
    PropSPropRel (@S.rta_recurrence_solution Task tcR maR tsR PiR ThR nuR LR RR)
      (I.Prosa_Results_Rta_Arm_Fifo_BoundedNps_rta_recurrence_solution
        Task dT tcL maL tsL PiL ThL nuL LL RL).
  Proof.
    unfold S.rta_recurrence_solution.
    cbn [I.Prosa_Results_Rta_Arm_Fifo_BoundedNps_rta_recurrence_solution].
    apply ad_forall_nat_correspondence. intros AR AL HA.
    apply ad_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (SSF.is_in_search_space_correspondence Task tcR tcL Htc tsR tsL Hts maR maL Hma LR AR LL AL HL HA))|].
    apply ar_exists_nat_correspondence. intros FR' FL' HF.
    apply ar_and_correspondence.
    - exact (sub_nat_le_correspondence _ _ _ _
        (RBF.total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts _ _
          (svc_target_add_related _ _ _ _ HA ONE))
        (ARM _ _ HPi _ _ HTh _ _ Hnu _ _ HF)).
    - exact (sub_nat_le_correspondence _ _ _ _ HF (svc_target_add_related _ _ _ _ HA HR)).
  Qed.

  (** *** The theorem *)

  Definition src_uniprocessor_response_time_bound_fifo : Prop :=
    ltac:(body_of (fun s : S.statement_uniprocessor_response_time_bound_fifo =>
      s Task tcR maR rR Job jtR costR jaR jpR)).
  Definition tgt_uniprocessor_response_time_bound_fifo : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Results_Rta_Arm_Fifo_BoundedNps_uniprocessor_response_time_bound_fifo
        Task dT tcL maL rL Job dJ jtL costL jaL jpL)).

  Theorem uniprocessor_response_time_bound_fifo_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_fifo
      tgt_uniprocessor_response_time_bound_fifo.
  Proof.
    unfold src_uniprocessor_response_time_bound_fifo,
      tgt_uniprocessor_response_time_bound_fifo.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply (rs_forall_pstate Job). intros PStateR PStateL [R Hsupply_on].
    imp (ibt_uni Job PStateR PStateL R).
    imp (rsi_unit_supply_rel Job PStateR PStateL R Hsupply_on).
    imp (rsi_fully_consuming_rel Job PStateR PStateL R Hsupply_on).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (rfa_valid_task_arrival_sequence_rel tsR tsL Hts arrR arrL Harr).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rR rL Hr
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    have Hjr := rfe_basic_ready_at PStateR PStateL R sR sL Hs.
    imp (rsi_valid_schedule_rel Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (rsi_work_conserving_related Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL (rsi_jsvc Job PStateR PStateL R)
      sR sL (rsi_hs_jsvc Job PStateR PStateL R sR sL Hs) arrR arrL Harr).
    imp (rfe_respects_jlfp_rel PStateR PStateL R sR sL Hs arrR arrL Harr _ _ Hjp _ _ Hjr _ _ rff_fifo_rel).
    apply ad_forall_nat_correspondence. intros PiR PiL HPi.
    apply ad_forall_nat_correspondence. intros ThR ThL HTh.
    apply ad_forall_nat_correspondence. intros nuR nuL Hnu.
    imp (AVG.average_resource_model_correspondence Job PStateR PStateL
      (rsi_sup Job PStateR PStateL R Hsupply_on) sR sL (rsi_hs_sup Job PStateR PStateL R Hsupply_on sR sL Hs)
      PiR ThR nuR PiL ThL nuL HPi HTh Hnu).
    apply ad_forall_nat_correspondence. intros LR LL HL.
    imp (busy_window_recurrence_solution_correspondence tsR tsL Hts PiR PiL HPi ThR ThL HTh nuR nuL Hnu LR LL HL).
    apply ad_forall_nat_correspondence. intros RR RL HR.
    imp (rta_recurrence_solution_correspondence tsR tsL Hts PiR PiL HPi ThR ThL HTh nuR nuL Hnu LR LL HL RR RL HR).
    unfold SCH.task_response_time_bound.
    cbn [I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound].
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt)).
    unfold prosa.behavior.service.job_response_time_bound.
    cbn [I.Prosa_Behavior_Service_job_response_time_bound].
    exact (ar_bool_truth_correspondence _ _
      (ibt_completed Job PStateR PStateL R costR costL Hcost sR sL Hs j _ _
        (svc_target_add_related _ _ _ _ (Hja j) HR))).
  Qed.
End RtaArmFifoBoundedNps.
