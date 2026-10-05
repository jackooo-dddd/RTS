From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import BoundedBiEdfSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply analysis.definitions.sbf.pred
  model.task.absolute_deadline model.priority.edf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBoundedBiEdf ImportedSubadditivity.
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
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence EdfPiBoundCorrespondence
  ServiceInversionPredCorrespondence.
From FoundationCertificates Require Import PcoBaseAdapter.
From FoundationCertificates Require Import IbfTaskFullHelpers RsIwHelpers.

Module I := ImportedBoundedBiEdf.
Module S := BoundedBiEdfSemanticSource.BoundedBiEdfSemanticSource.
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
Module EPI := FoundationCertificates.EdfPiBoundCorrespondence.
Module SIPC := FoundationCertificates.ServiceInversionPredCorrespondence.
Module IFC := FoundationCertificates.InterferenceCorrespondence.
Module WLC := FoundationCertificates.WorkloadCorrespondence.
Module JSO := FoundationCertificates.JitterSvcScheduleOperations.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module PPS := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

(** Statement correspondences for
    [analysis/abstract/restricted_supply/bounded_bi/edf.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, [task_cost], [task_deadline], [job_task],
    [job_arrival], [job_cost], a leading processor state); target side: the imported Lean theorem type.
    Inputs: [task_cost], [task_deadline], [job_arrival], [job_cost]
    pointwise; [job_task] by
    the accepted [AdJobTaskRel]; the processor state by the accepted
    two-sided [SvcProcessorStateRel] together with the pointwise [supply_on]
    relation, from which the accepted restricted-supply family relations
    (service and supply views) are built.  Arrival sequences, schedules
    and readiness instances (the accepted covers of the restricted-supply
    instantiation certificate), [JobPreemptable] and
    [TaskMaxNonpreemptiveSegment] instances, task sets, [MaxArrivals]
    instances and supply-bound functions are covered in both directions;
    The classical busy-interval prefix, the cumulative service
    inversion, the other higher-or-equal-priority interfering workload and
    the job workload are the accepted certificates re-instantiated at this
    artifact.  Tasks and jobs are identity carriers and Nats are covered in both
    directions.

    The source's two section-local instances re-expose the accepted
    restricted-supply instantiation at the EDF policy over task deadlines
    (related pointwise from the arrival and deadline inputs) and are related by the accepted
    [rsi_interference_rel]/[rsi_workload_rel].  Preemption models, bounded
    nonpreemptive segments, preemption times and the EDF priority-inversion bound
    are the accepted certificates (the service view of the processor relation);
    the JLFP policy at preemption points is the accepted priority-driven
    certificate's proof replayed with the readiness relation at the related
    schedule pair (the only schedule pair it observes).  The remaining
    hypotheses and conclusions are the accepted certificates of the JLFP
    bounded-busy-interval certificates, re-instantiated at this artifact.  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Covers *)

Definition bbd_fun1_to_target (fR : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun xL => sub_nat_to_imported (fR (sub_nat_to_rocq xL)).
Definition bbd_fun1_to_source (fL : Lean.Nat -> Lean.Nat) : nat -> nat :=
  fun xR => sub_nat_to_rocq (fL (sub_nat_to_imported xR)).

Lemma bbd_fun1_to_target_rel fR : JSI.SvcNatFunRel fR (bbd_fun1_to_target fR).
Proof.
  intros xR xL Hx. unfold bbd_fun1_to_target.
  rewrite (arta_nat_input _ _ Hx). exact (sub_nat_rel_canonical _).
Qed.

Lemma bbd_fun1_to_source_rel fL : JSI.SvcNatFunRel (bbd_fun1_to_source fL) fL.
Proof. intros xR xL Hx. destruct Hx. exact (sub_nat_imported_roundtrip _). Qed.

Lemma bbd_forall_fun1 (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, JSI.SvcNatFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  exact (arta_forall_cover _ _ JSI.SvcNatFunRel bbd_fun1_to_target bbd_fun1_to_source
    bbd_fun1_to_target_rel bbd_fun1_to_source_rel PR PL).
Qed.

Definition BbdSbfRel (sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction)
    (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) : SProp :=
  PC.PredFunctionRel sR (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL).

Definition bbd_sbf_to_target (fR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction) :
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction :=
  I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
    (fun dL => sub_nat_to_imported (fR (sub_nat_to_rocq dL))).
Definition bbd_sbf_to_source (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :
    prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction :=
  ((fun dR => sub_nat_to_rocq
    (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL (sub_nat_to_imported dR)))
    : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction).

Lemma bbd_forall_sbf (PR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction -> Prop)
    (PL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> SProp) :
  (forall sR sL, BbdSbfRel sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  apply (arta_forall_cover _ _ BbdSbfRel bbd_sbf_to_target bbd_sbf_to_source).
  - intros fR nR nL Hn. unfold BbdSbfRel, bbd_sbf_to_target. cbn.
    rewrite (arta_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
  - intros sL nR nL Hn. destruct Hn. exact (sub_nat_imported_roundtrip _).
Qed.

Section BoundedBiEdf.
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
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
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

  Lemma bbd_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (arta_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma bbd_valid_job_costs_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (bbd_task_cost_of_job_related j))).
  Qed.

  Lemma bbd_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
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

  Definition BbdMaxArrivalsRel (maR : prosa.model.task.arrival.curves.MaxArrivals Task)
      (maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT) : SProp :=
    forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
      SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).

  Lemma bbd_forall_ma (PR : prosa.model.task.arrival.curves.MaxArrivals Task -> Prop)
      (PL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT -> SProp) :
    (forall maR maL, BbdMaxArrivalsRel maR maL -> PropSPropRel (PR maR) (PL maL)) ->
    PropSPropRel (forall m, PR m) (forall m, PL m).
  Proof.
    apply (arta_forall_cover _ _ BbdMaxArrivalsRel
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


  Let HsJ sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) :=
    rsi_hs_jsvc Job PStateR PStateL R sR sL Hs.
  Let J := rsi_jsvc Job PStateR PStateL R.

  (** *** Preemption-model covers (as in the accepted busy-interval certificates) *)

  Lemma bbd_forall_jp (PR : PPS.JobPreemptable Job -> Prop)
      (PL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ -> SProp) :
    (forall jpR jpL, PPC.PpJobPreemptableRel Job jpR jpL -> PropSPropRel (PR jpR) (PL jpL)) ->
    PropSPropRel (forall jp, PR jp) (forall jp, PL jp).
  Proof.
    exact (arta_forall_cover _ _ (PPC.PpJobPreemptableRel Job)
      (fun jpR => I.Prosa_Model_Preemption_Parameter_JobPreemptable_mk Job dJ
        (fun j nL => ar_bool_to_imported (jpR j (sub_nat_to_rocq nL))))
      (fun jpL => ((fun j n => ar_bool_to_rocq
        (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j
          (sub_nat_to_imported n))) : PPS.JobPreemptable Job))
      (PPC.JobPreemptable_source_total Job) (PPC.JobPreemptable_target_total Job) PR PL).
  Qed.

  Lemma bbd_forall_tms (PRm : TPS.TaskMaxNonpreemptiveSegment Task -> Prop)
      (PLm : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT -> SProp) :
    (forall mR mL, TPPC.TppMaxSegmentRel Task mR mL -> PropSPropRel (PRm mR) (PLm mL)) ->
    PropSPropRel (forall m, PRm m) (forall m, PLm m).
  Proof.
    exact (arta_forall_cover _ _ (TPPC.TppMaxSegmentRel Task)
      (fun cR => I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_mk Task dT
        (fun tsk => sub_nat_to_imported (@TPS.task_max_nonpreemptive_segment Task cR tsk)))
      (fun cL => ((fun tsk => sub_nat_to_rocq
        (I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment
          Task dT cL tsk)) : TPS.TaskMaxNonpreemptiveSegment Task))
      (TPPC.TaskMaxNonpreemptiveSegment_source_total Task) (TPPC.TaskMaxNonpreemptiveSegment_target_total Task)
      PRm PLm).
  Qed.

  (** *** The FP policy at preemption points

      The accepted priority-driven certificate's proof, replayed with the
      readiness relation at the related schedule pair (the only schedule
      pair that proof observes). *)

  Lemma bbd_respects_jlfp_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL)
      arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
      jpR jpL (Hjp : PPC.PpJobPreemptableRel Job jpR jpL)
      jrR jrL (Hjr : RsiJrAt Job PStateR PStateL jaR jaL costR costL sR sL jrR jrL)
      pR pL (Hp : RsiJLFPRel Job pR pL) :
    PropSPropRel (@PDS.respects_JLFP_policy_at_preemption_point Job jaR costR PStateR jpR jrR arrR sR pR)
      (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
        Job dJ jaL costL PStateL jpL jrL arrL sL pL).
  Proof.
    unfold PDS.respects_JLFP_policy_at_preemption_point, PDS.respects_JLDP_policy_at_preemption_point.
    cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
      I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j_hp.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _
      (PTC.preemption_time_correspondence Job jpR jpL Hjp PStateR PStateL J sR sL (HsJ sR sL Hs)
        arrR arrL Harr tR tL Ht)).
    imp (ar_bool_truth_correspondence _ _
      (rsi_backlogged_related Job PStateR PStateL R jaR jaL costR costL sR sL Hs jrR jrL Hjr j tR tL Ht)).
    imp (ar_bool_truth_correspondence _ _
      (PPC.pp_scheduled_at_related Job PStateR PStateL J sR sL (HsJ sR sL Hs) j_hp tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _ (Hp j_hp j)).
  Qed.

  (** *** The EDF policy over task deadlines *)

  Let ER := @prosa.model.priority.edf.EDF Job
    (@prosa.model.task.absolute_deadline.job_deadline_from_task_deadline Job Task tdR jaR jtR).

  Let EL := I.Prosa_Model_Priority_Edf_EDF Job dJ
    (I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task dJ dT tdL jaL jtL).

  Lemma bbd_task_deadline_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (arta_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_deadline Task tdR
          (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL v)) _ _ (Hjt j) (Htd _)).
  Qed.

  Lemma bbd_edf_rel : RsiJLFPRel Job ER EL.
  Proof.
    intros x y. cbn.
    exact (svc_decide_le_related _ _ _ _
      (svc_target_add_related _ _ _ _ (Hja x) (bbd_task_deadline_of_job_related x))
      (svc_target_add_related _ _ _ _ (Hja y) (bbd_task_deadline_of_job_related y))).
  Qed.

  (** *** longest_bi_with_pi_bound_is_valid *)

  Definition src_longest_bi_with_pi_bound_is_valid : Prop :=
    ltac:(body_of (fun s : S.statement_longest_bi_with_pi_bound_is_valid =>
      s Task tcR tdR Job jtR jaR costR PStateR)).
  Definition tgt_longest_bi_with_pi_bound_is_valid : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Edf_longest_bi_with_pi_bound_is_valid
        Task dT tcL tdL Job dJ jtL jaL costL PStateL)).

  Theorem longest_bi_with_pi_bound_is_valid_correspondence :
    PropSPropRel src_longest_bi_with_pi_bound_is_valid tgt_longest_bi_with_pi_bound_is_valid.
  Proof.
    unfold src_longest_bi_with_pi_bound_is_valid, tgt_longest_bi_with_pi_bound_is_valid.
    imp (ibt_uni Job PStateR PStateL R).
    imp (rsi_unit_supply_rel Job PStateR PStateL R Hsupply_on).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    apply (rsi_forall_jr Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs). intros jrR jrL Hjr.
    have Hp := bbd_edf_rel.
    imp (rsi_work_bearing_related Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
      _ _ Hp jrR jrL Hjr).
    imp (rsi_valid_schedule_rel Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply bbd_forall_jp. intros jpR jpL Hjp.
    apply bbd_forall_tms. intros mR mL Hm.
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL J
      sR sL (HsJ sR sL Hs) arrR arrL Harr).
    imp (TPPC.valid_model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt
      costR costL Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr PStateR PStateL J sR sL (HsJ sR sL Hs)).
    imp (bbd_respects_jlfp_rel sR sL Hs arrR arrL Harr jpR jpL Hjp jrR jrL Hjr _ _ Hp).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (bbd_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (bbd_valid_job_costs_rel arrR arrL Harr).
    apply bbd_forall_ma. intros maR maL Hma.
    imp (CV.taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
      maR maL Hma).
    apply ad_forall_identity_correspondence. intro tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply bbd_forall_sbf. intros sbR sbL Hsb.
    imp (SBFB.valid_busy_sbf_correspondence Task Job PStateR PStateL
      (rsi_sup Job PStateR PStateL R Hsupply_on) J sR sL
      (rsi_hs_sup Job PStateR PStateL R Hsupply_on sR sL Hs) (HsJ sR sL Hs) arrR arrL Harr jaR jaL Hja
      costR costL Hcost jtR jtL Hjt _ _ Hp tsk _ _ Hsb).
    apply ad_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt)).
    imp (ar_bool_truth_correspondence _ _ (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))).
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    imp (rsi_busy_interval_prefix_related Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs
      arrR arrL Harr _ _ Hp j _ _ _ _ H1 H2).
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have H1d := svc_target_add_related _ _ _ _ H1 Hd.
    imp (sub_nat_le_correspondence _ _ _ _ H1d H2).
    have HSI := SIPC.cumulative_service_inversion_correspondence Job PStateR PStateL J sR sL (HsJ sR sL Hs)
      arrR arrL Harr _ _ (rsi_jlfp_to_jldp_rel Job _ _ Hp) j _ _ _ _ H1 H1d.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HSI).
    exact (sub_nat_le_correspondence _ _ _ _
      (svc_target_add_related _ _ _ _ HSI
        (svc_target_add_related _ _ _ _
          (IFC.cumulative_other_hep_jobs_interfering_workload_correspondence Job costR costL Hcost
            arrR arrL Harr _ _ Hp j _ _ _ _ H1 H1d)
          (WLC.workload_of_job_correspondence Job costR costL Hcost arrR arrL Harr j _ _ _ _ H1 H1d)))
      (EPI.longest_busy_interval_with_pi_correspondence Task tcR tcL Htc tdR tdL Htd mR mL Hm maR maL Hma
        tsR tsL Hts tsk)).
  Qed.

  (** *** busy_intervals_are_bounded_rs_edf *)

  Definition src_busy_intervals_are_bounded_rs_edf : Prop :=
    ltac:(body_of (fun s : S.statement_busy_intervals_are_bounded_rs_edf =>
      s Task tcR tdR Job jtR jaR costR PStateR)).
  Definition tgt_busy_intervals_are_bounded_rs_edf : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Edf_busy_intervals_are_bounded_rs_edf
        Task dT tcL tdL Job dJ jtL jaL costL PStateL)).

  Theorem busy_intervals_are_bounded_rs_edf_correspondence :
    PropSPropRel src_busy_intervals_are_bounded_rs_edf tgt_busy_intervals_are_bounded_rs_edf.
  Proof.
    unfold src_busy_intervals_are_bounded_rs_edf, tgt_busy_intervals_are_bounded_rs_edf.
    have Hp := bbd_edf_rel.
    imp (ibt_uni Job PStateR PStateL R).
    imp (rsi_unit_supply_rel Job PStateR PStateL R Hsupply_on).
    imp (rsi_fully_consuming_rel Job PStateR PStateL R Hsupply_on).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    apply (rsi_forall_jr Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs). intros jrR jrL Hjr.
    imp (rsi_work_bearing_related Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
      _ _ Hp jrR jrL Hjr).
    imp (rsi_valid_schedule_rel Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply bbd_forall_jp. intros jpR jpL Hjp.
    apply bbd_forall_tms. intros mR mL Hm.
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL J
      sR sL (HsJ sR sL Hs) arrR arrL Harr).
    imp (TPPC.valid_model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt
      costR costL Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr PStateR PStateL J sR sL (HsJ sR sL Hs)).
    imp (bbd_respects_jlfp_rel sR sL Hs arrR arrL Harr jpR jpL Hjp jrR jrL Hjr _ _ Hp).
    have HI := rsi_interference_rel Job PStateR PStateL R Hsupply_on sR sL Hs arrR arrL Harr _ _ Hp.
    have HW := rsi_workload_rel Job PStateR PStateL R Hsupply_on costR costL Hcost sR sL Hs arrR arrL Harr _ _ Hp.
    imp (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
      _ _ HI _ _ HW arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (bbd_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (bbd_valid_job_costs_rel arrR arrL Harr).
    apply bbd_forall_ma. intros maR maL Hma.
    imp (CV.taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
      maR maL Hma).
    apply ad_forall_identity_correspondence. intro tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply bbd_forall_sbf. intros sbR sbL Hsb.
    imp (SBFB.valid_busy_sbf_correspondence Task Job PStateR PStateL
      (rsi_sup Job PStateR PStateL R Hsupply_on) J sR sL
      (rsi_hs_sup Job PStateR PStateL R Hsupply_on sR sL Hs) (HsJ sR sL Hs) arrR arrL Harr jaR jaL Hja
      costR costL Hcost jtR jtL Hjt _ _ Hp tsk _ _ Hsb).
    imp (PC.pred_unit_supply_bound_function_correspondence _ _ Hsb).
    apply ad_forall_nat_correspondence. intros LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_le_correspondence _ _ _ _
      (EPI.longest_busy_interval_with_pi_correspondence Task tcR tcL Htc tdR tdL Htd mR mL Hm maR maL Hma
        tsR tsL Hts tsk) (Hsb _ _ HL)).
    imp (sub_nat_le_correspondence _ _ _ _
      (RBF.total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)
      (Hsb _ _ HL)).
    exact (ad_busy_intervals_bounded_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
      _ _ HI _ _ HW arrR arrL Harr Task jtR jtL Hjt tsk LR LL HL).
  Qed.
End BoundedBiEdf.
