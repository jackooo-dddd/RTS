From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FifoFixpointSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply analysis.definitions.sbf.pred
  model.priority.fifo.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFifoFixpoint ImportedSubadditivity.
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
  SearchSpaceFifoCorrespondence.
From FoundationCertificates Require Import IbfTaskFullHelpers RsIwHelpers.

Module I := ImportedFifoFixpoint.
Module S := FifoFixpointSemanticSource.FifoFixpointSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module JSI := FoundationCertificates.JitterSvcIntervalOperations.
Module CV := FoundationCertificates.CurvesCorrespondence.
Module RBF := FoundationCertificates.RequestBoundFunctionCorrespondence.
Module PC := FoundationCertificates.PredHelpers.
Module SBFB := FoundationCertificates.SbfBusyCorrespondence.

Module TPPC := FoundationCertificates.TaskPreemptionParametersCorrespondence.
Module PPC := FoundationCertificates.PreemptionParameterCorrespondence.
Module SSF := FoundationCertificates.SearchSpaceFifoCorrespondence.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PPS := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

(** Statement correspondence for
    [analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, [task_cost], [max_arrivals], the run-to-completion
    threshold, [job_task], [job_cost], [job_arrival], the preemption model, a
    leading processor state); target side: the imported Lean theorem type.
    Inputs: [task_cost], [job_cost], [job_arrival] pointwise; [max_arrivals]
    by the accepted [CvMaxArrivalsRel]; the run-to-completion threshold by the
    accepted [TppRtctRel]; the preemption model by the accepted
    [PpJobPreemptableRel]; [job_task] by the accepted [AdJobTaskRel]; the
    processor state by the accepted two-sided [SvcProcessorStateRel] together
    with the pointwise [supply_on] relation (the accepted restricted-supply
    family relations).  Supply bound functions (pointwise on Nats through
    their class field), task sets, arrival sequences, schedules, tasks and
    instants are covered in both directions.

    The FIFO policy is related pointwise from the arrival input; the classical
    busy-SBF validity, the supply-bound-function predicates, the
    run-to-completion validity, the request-bound functions and the FIFO
    search space are the accepted certificates re-instantiated at this
    artifact.  The source-local [intra_IBF] of this file and the FIFO search
    space's source-local [IBF] are unfolded by conversion and related through
    their bodies; the abstract search-space predicate is related by unfolding,
    as in the accepted FIFO search space.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Definition FfxSbfRel (sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction)
    (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) : SProp :=
  PC.PredFunctionRel sR (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL).

Definition ffx_sbf_to_target (fR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction) :
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction :=
  I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
    (fun dL => sub_nat_to_imported (fR (sub_nat_to_rocq dL))).
Definition ffx_sbf_to_source (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :
    prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction :=
  ((fun dR => sub_nat_to_rocq
    (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL (sub_nat_to_imported dR)))
    : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction).

Lemma ffx_forall_sbf (PR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction -> Prop)
    (PL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> SProp) :
  (forall sR sL, FfxSbfRel sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  apply (arta_forall_cover _ _ FfxSbfRel ffx_sbf_to_target ffx_sbf_to_source).
  - intros fR nR nL Hn. unfold FfxSbfRel, ffx_sbf_to_target. cbn.
    rewrite (arta_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
  - intros sL nR nL Hn. destruct Hn. exact (sub_nat_imported_roundtrip _).
Qed.

Section FifoFixpoint.
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
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.
  Variable rR : TPS.TaskRunToCompletionThreshold Task.
  Variable rL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hr : TPPC.TppRtctRel Task rR rL.
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
  Variable jpR : PPS.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PPC.PpJobPreemptableRel Job jpR jpL.

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  Let FR := @prosa.model.priority.fifo.FIFO Job jaR.
  Let FL := I.Prosa_Model_Priority_Fifo_FIFO Job dJ jaL.

  Lemma ffx_fifo_rel : RsiJLFPRel Job FR FL.
  Proof. intros x y. exact (svc_decide_le_related _ _ _ _ (Hja x) (Hja y)). Qed.

  Let ONE := sub_nat_rel_canonical (S O).

  Definition src_soln_abstract_response_time_recurrence : Prop :=
    ltac:(body_of (fun s : S.statement_soln_abstract_response_time_recurrence =>
      s Task tcR maR rR Job jtR costR jaR jpR PStateR)).
  Definition tgt_soln_abstract_response_time_recurrence : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_FifoFixpoint_soln_abstract_response_time_recurrence
        Task dT tcL maL rL Job dJ jtL costL jaL jpL PStateL)).

  Theorem soln_abstract_response_time_recurrence_correspondence :
    PropSPropRel src_soln_abstract_response_time_recurrence tgt_soln_abstract_response_time_recurrence.
  Proof.
    unfold src_soln_abstract_response_time_recurrence, tgt_soln_abstract_response_time_recurrence.
    apply ffx_forall_sbf. intros sbR sbL Hsb.
    imp (PC.pred_sbf_is_monotone_correspondence _ _ Hsb).
    imp (PC.pred_unit_supply_bound_function_correspondence _ _ Hsb).
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (CV.valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    imp (SBFB.valid_busy_sbf_correspondence Task Job PStateR PStateL
      (rsi_sup Job PStateR PStateL R Hsupply_on) (rsi_jsvc Job PStateR PStateL R) sR sL
      (rsi_hs_sup Job PStateR PStateL R Hsupply_on sR sL Hs) (rsi_hs_jsvc Job PStateR PStateL R sR sL Hs)
      arrR arrL Harr jaR jaL Hja costR costL Hcost jtR jtL Hjt FR FL ffx_fifo_rel tsk _ _ Hsb).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rR rL Hr
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    apply ad_forall_nat_correspondence. intros LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hma tsk (S O) _ ONE)).
    apply ad_forall_nat_correspondence. intros RR RL HR.
    have TRBF := fun aR aL (Ha : SubNatRel aR aL) =>
      RBF.total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts aR aL Ha.
    apply ad_imp_correspondence.
    { apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (SSF.is_in_search_space_correspondence Task tcR tcL Htc tsR tsL Hts maR maL Hma LR AR LL AL HL HA))|].
      apply ar_exists_nat_correspondence. intros FR' FL' HF.
      apply ar_and_correspondence.
      - exact (sub_nat_le_correspondence _ _ _ _ (TRBF _ _ (svc_target_add_related _ _ _ _ HA ONE))
          (Hsb _ _ HF)).
      - exact (sub_nat_le_correspondence _ _ _ _ HF (svc_target_add_related _ _ _ _ HA HR)). }
    apply ad_forall_nat_correspondence. intros AR AL HA.
    have IBF := fun aR aL (Ha : SubNatRel aR aL) xR xL (Hx : SubNatRel xR xL) =>
      svc_target_add_related _ _ _ _
        (svc_target_sub_related _ _ _ _ Hx (Hsb _ _ Hx))
        (svc_target_sub_related _ _ _ _
          (TRBF _ _ (svc_target_add_related _ _ _ _ Ha ONE)) (Htc tsk)).
    apply ad_imp_correspondence.
    - unfold prosa.analysis.abstract.search_space.is_in_search_space,
        prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than.
      cbn [I.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
        I.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than].
      apply SSF.ssfi_or_correspondence;
        [exact (sub_nat_eq_correspondence _ _ _ _ HA (sub_nat_rel_canonical O))|].
      apply SSF.ssfi_and3_correspondence.
      + exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HA).
      + exact (sub_nat_lt_correspondence _ _ _ _ HA HL).
      + apply ar_exists_nat_correspondence. intros xR xL Hx.
        apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hx HL)|].
        have HA1 := svc_target_sub_related _ _ _ _ HA ONE.
        exact (SSF.ssfi_nat_neq_correspondence _ _ _ _ (IBF _ _ HA1 _ _ Hx) (IBF _ _ HA _ _ Hx)).
    - apply ar_exists_nat_correspondence. intros FR' FL' HF.
      have HAR := svc_target_add_related _ _ _ _ HA HR.
      apply ar_and_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ HF HAR)|].
      apply ar_and_correspondence.
      + exact (sub_nat_le_correspondence _ _ _ _
          (svc_target_add_related _ _ _ _ (Hr tsk)
            (svc_target_sub_related _ _ _ _ (TRBF _ _ (svc_target_add_related _ _ _ _ HA ONE)) (Htc tsk)))
          (Hsb _ _ HF)).
      + exact (sub_nat_le_correspondence _ _ _ _
          (svc_target_add_related _ _ _ _ (Hsb _ _ HF) (svc_target_sub_related _ _ _ _ (Htc tsk) (Hr tsk)))
          (Hsb _ _ HAR)).
  Qed.
End FifoFixpoint.
