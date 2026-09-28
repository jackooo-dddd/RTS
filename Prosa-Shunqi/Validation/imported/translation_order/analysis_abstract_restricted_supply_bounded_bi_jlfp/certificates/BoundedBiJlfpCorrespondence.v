From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import BoundedBiJlfpSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply analysis.definitions.sbf.pred.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBoundedBiJlfp ImportedSubadditivity.
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
  ArrivalSequenceCorrespondence BusyIntervalClassicalHelpers PredHelpers SbfBusyCorrespondence.
From FoundationCertificates Require Import IbfTaskFullHelpers RsIwHelpers.

Module I := ImportedBoundedBiJlfp.
Module S := BoundedBiJlfpSemanticSource.BoundedBiJlfpSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module JSI := FoundationCertificates.JitterSvcIntervalOperations.
Module CV := FoundationCertificates.CurvesCorrespondence.
Module RBF := FoundationCertificates.RequestBoundFunctionCorrespondence.
Module SIBP := FoundationCertificates.ServiceInversionBusyPrefixCorrespondence.
Module PC := FoundationCertificates.PredHelpers.
Module SBFB := FoundationCertificates.SbfBusyCorrespondence.

(** Statement correspondence for
    [analysis/abstract/restricted_supply/bounded_bi/jlfp.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, [task_cost], [job_task], [job_arrival], [job_cost],
    a leading processor state); target side: the imported Lean theorem type.
    Inputs: [task_cost], [job_arrival], [job_cost] pointwise; [job_task] by
    the accepted [AdJobTaskRel]; the processor state by the accepted
    two-sided [SvcProcessorStateRel] together with the pointwise [supply_on]
    relation, from which the accepted restricted-supply family relations
    (service and supply views) are built.  JLFP policies (pointwise on
    Booleans), arrival sequences, schedules and readiness instances are
    covered by the accepted covers of the restricted-supply instantiation
    certificate; task sets, [MaxArrivals] instances, supply-bound functions
    and the blocking-bound function (pointwise on related Nats) are covered
    in both directions; tasks and jobs are identity carriers and Nats are
    covered in both directions.

    The source's two section-local instances re-expose the accepted
    restricted-supply instantiation and are related by the accepted
    [rsi_interference_rel]/[rsi_workload_rel].  The processor-model
    hypotheses, schedule validity, abstract work conservation, the classical
    service-inversion bound, arrival-curve conformance, the request-bound
    function, the classical busy-SBF validity (the accepted
    [valid_busy_sbf_correspondence] over the service and supply views), unit
    supply-bound functions and bounded busy intervals are the accepted
    certificates re-instantiated at this artifact.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Covers *)

Definition bbj_fun1_to_target (fR : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun xL => sub_nat_to_imported (fR (sub_nat_to_rocq xL)).
Definition bbj_fun1_to_source (fL : Lean.Nat -> Lean.Nat) : nat -> nat :=
  fun xR => sub_nat_to_rocq (fL (sub_nat_to_imported xR)).

Lemma bbj_fun1_to_target_rel fR : JSI.SvcNatFunRel fR (bbj_fun1_to_target fR).
Proof.
  intros xR xL Hx. unfold bbj_fun1_to_target.
  rewrite (arta_nat_input _ _ Hx). exact (sub_nat_rel_canonical _).
Qed.

Lemma bbj_fun1_to_source_rel fL : JSI.SvcNatFunRel (bbj_fun1_to_source fL) fL.
Proof. intros xR xL Hx. destruct Hx. exact (sub_nat_imported_roundtrip _). Qed.

Lemma bbj_forall_fun1 (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, JSI.SvcNatFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  exact (arta_forall_cover _ _ JSI.SvcNatFunRel bbj_fun1_to_target bbj_fun1_to_source
    bbj_fun1_to_target_rel bbj_fun1_to_source_rel PR PL).
Qed.

Definition BbjSbfRel (sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction)
    (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) : SProp :=
  PC.PredFunctionRel sR (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL).

Definition bbj_sbf_to_target (fR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction) :
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction :=
  I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
    (fun dL => sub_nat_to_imported (fR (sub_nat_to_rocq dL))).
Definition bbj_sbf_to_source (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :
    prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction :=
  ((fun dR => sub_nat_to_rocq
    (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL (sub_nat_to_imported dR)))
    : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction).

Lemma bbj_forall_sbf (PR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction -> Prop)
    (PL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> SProp) :
  (forall sR sL, BbjSbfRel sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  apply (arta_forall_cover _ _ BbjSbfRel bbj_sbf_to_target bbj_sbf_to_source).
  - intros fR nR nL Hn. unfold BbjSbfRel, bbj_sbf_to_target. cbn.
    rewrite (arta_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
  - intros sL nR nL Hn. destruct Hn. exact (sub_nat_imported_roundtrip _).
Qed.

Section BoundedBiJlfp.
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

  Lemma bbj_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (arta_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma bbj_valid_job_costs_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (bbj_task_cost_of_job_related j))).
  Qed.

  Lemma bbj_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
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

  Definition BbjMaxArrivalsRel (maR : prosa.model.task.arrival.curves.MaxArrivals Task)
      (maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT) : SProp :=
    forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
      SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).

  Lemma bbj_forall_ma (PR : prosa.model.task.arrival.curves.MaxArrivals Task -> Prop)
      (PL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT -> SProp) :
    (forall maR maL, BbjMaxArrivalsRel maR maL -> PropSPropRel (PR maR) (PL maL)) ->
    PropSPropRel (forall m, PR m) (forall m, PL m).
  Proof.
    apply (arta_forall_cover _ _ BbjMaxArrivalsRel
      (fun maR => I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk Task dT
        (fun tsk nL => sub_nat_to_imported (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk
          (sub_nat_to_rocq nL))))
      (fun maL => ((fun tsk n => sub_nat_to_rocq
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk (sub_nat_to_imported n)))
        : prosa.model.task.arrival.curves.MaxArrivals Task))).
    - intros maR tsk nR nL Hn. cbn. rewrite (arta_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
    - intros maL tsk nR nL Hn. unfold SubNatRel. cbn.
      exact (sub_imported_eq_trans _ _ _ (sub_nat_imported_roundtrip _)
        (sub_imported_eq_congr (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk)
          _ _ Hn)).
  Qed.

  (** *** busy_intervals_are_bounded_rs_jlfp *)

  Definition src_busy_intervals_are_bounded_rs_jlfp : Prop :=
    ltac:(body_of (fun s : S.statement_busy_intervals_are_bounded_rs_jlfp =>
      s Task tcR Job jtR jaR costR PStateR)).
  Definition tgt_busy_intervals_are_bounded_rs_jlfp : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Jlfp_busy_intervals_are_bounded_rs_jlfp
        Task dT tcL Job dJ jtL jaL costL PStateL)).

  Theorem busy_intervals_are_bounded_rs_jlfp_correspondence :
    PropSPropRel src_busy_intervals_are_bounded_rs_jlfp tgt_busy_intervals_are_bounded_rs_jlfp.
  Proof.
    unfold src_busy_intervals_are_bounded_rs_jlfp, tgt_busy_intervals_are_bounded_rs_jlfp.
    imp (ibt_uni Job PStateR PStateL R).
    imp (rsi_unit_supply_rel Job PStateR PStateL R Hsupply_on).
    imp (rsi_fully_consuming_rel Job PStateR PStateL R Hsupply_on).
    apply (rsi_forall_jlfp Job). intros pR pL Hp.
    imp (rsi_reflexive_rel Job pR pL Hp).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    apply (rsi_forall_jr Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs). intros jrR jrL Hjr.
    imp (rsi_valid_schedule_rel Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr jrR jrL Hjr).
    have HI := rsi_interference_rel Job PStateR PStateL R Hsupply_on sR sL Hs arrR arrL Harr pR pL Hp.
    have HW := rsi_workload_rel Job PStateR PStateL R Hsupply_on costR costL Hcost sR sL Hs arrR arrL Harr pR pL Hp.
    have HsJ := rsi_hs_jsvc Job PStateR PStateL R sR sL Hs.
    imp (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
      _ _ HI _ _ HW arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (bbj_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (bbj_valid_job_costs_rel arrR arrL Harr).
    apply bbj_forall_ma. intros maR maL Hma.
    imp (CV.taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
      maR maL Hma).
    apply ad_forall_identity_correspondence. intro tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply bbj_forall_sbf. intros fR fL Hf.
    imp (SBFB.valid_busy_sbf_correspondence Task Job PStateR PStateL
      (rsi_sup Job PStateR PStateL R Hsupply_on) (rsi_jsvc Job PStateR PStateL R) sR sL
      (rsi_hs_sup Job PStateR PStateL R Hsupply_on sR sL Hs) HsJ arrR arrL Harr jaR jaL Hja
      costR costL Hcost jtR jtL Hjt pR pL Hp tsk _ _ Hf).
    imp (PC.pred_unit_supply_bound_function_correspondence _ _ Hf).
    apply bbj_forall_fun1. intros BR BL HB.
    imp (SIBP.service_inversion_is_bounded_by_correspondence Task Job jtR jtL Hjt jaR jaL Hja costR costL Hcost
      PStateR PStateL (rsi_jsvc Job PStateR PStateL R) arrR arrL Harr sR sL HsJ pR pL Hp tsk BR BL HB).
    have HB0 := HB _ _ (sub_nat_rel_canonical O).
    imp (ad_forall_nat_correspondence _ _ (fun aR aL Ha =>
      sub_nat_le_correspondence _ _ _ _ (HB _ _ Ha) HB0)).
    apply ad_forall_nat_correspondence. intros LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_le_correspondence _ _ _ _
      (svc_target_add_related _ _ _ _ HB0
        (RBF.total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL))
      (Hf _ _ HL)).
    exact (ad_busy_intervals_bounded_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
      _ _ HI _ _ HW arrR arrL Harr Task jtR jtL Hjt tsk LR LL HL).
  Qed.
End BoundedBiJlfp.
