(* Helper-only copy of the accepted certificates/analysis_abstract_restricted_supply_bounded_bi_fp/BoundedBiFpCorrespondence.v (re-bound to this export),
   without its statement correspondence busy_intervals_are_bounded_rs_fp_correspondence (whose target statement is not
   part of this export); every other helper definition and lemma is unchanged. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import BoundedBiFpSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply analysis.definitions.sbf.pred.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaArmFpFloatingNonpreemptive ImportedSubadditivity.
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
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence BlockingBoundFpCorrespondence.
From FoundationCertificates Require Import PcoBaseAdapter.
From FoundationCertificates Require Import IbfTaskFullHelpers RsIwHelpers.

Module I := ImportedRtaArmFpFloatingNonpreemptive.
Module S := BoundedBiFpSemanticSource.BoundedBiFpSemanticSource.
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
Module BBF := FoundationCertificates.BlockingBoundFpCorrespondence.
Module JSO := FoundationCertificates.JitterSvcScheduleOperations.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module PPS := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

(** Statement correspondence for
    [analysis/abstract/restricted_supply/bounded_bi/fp.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, [task_cost], [job_task], [job_arrival], [job_cost],
    a leading processor state); target side: the imported Lean theorem type.
    Inputs: [task_cost], [job_arrival], [job_cost] pointwise; [job_task] by
    the accepted [AdJobTaskRel]; the processor state by the accepted
    two-sided [SvcProcessorStateRel] together with the pointwise [supply_on]
    relation, from which the accepted restricted-supply family relations
    (service and supply views) are built.  FP policies (pointwise on
    Booleans, the local [bbf_forall_fp] over the accepted [PcoBaseAdapter]), arrival sequences, schedules
    and readiness instances (the accepted covers of the restricted-supply
    instantiation certificate), [JobPreemptable] and
    [TaskMaxNonpreemptiveSegment] instances, task sets, [MaxArrivals]
    instances and supply-bound functions are covered in both directions;
    tasks and jobs are identity carriers and Nats are covered in both
    directions.

    The source's two section-local instances re-expose the accepted
    restricted-supply instantiation at the JLFP policy [FP_to_JLFP FP] (related by the local
    [bbf_fp_to_jlfp_rel]) and are related by the accepted
    [rsi_interference_rel]/[rsi_workload_rel].  Preemption models, bounded
    nonpreemptive segments, preemption times and the FP blocking bound are
    the accepted certificates (the service view of the processor relation);
    the FP policy at preemption points is the accepted priority-driven
    certificate's proof replayed with the readiness relation at the related
    schedule pair (the only schedule pair it observes).  The remaining
    hypotheses and the conclusion are the accepted certificates of the JLFP
    bounded-busy-interval certificate, re-instantiated at this artifact.  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Local FP-policy helpers

    The whole-file coercion and order certificates also relate constants that
    this artifact's export does not contain (e.g. [total_job_priorities]); as
    in the accepted FP blocking-bound facts certificate, the few facts used
    here are restated locally over the accepted [PcoBaseAdapter] relations. *)

Lemma bbf_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma bbf_forall_fp (Task : eqType)
    (PR : prosa.model.priority.definitions.FP_policy Task -> Prop)
    (PL : I.Prosa_Model_Priority_Definitions_FP_policy Task (pd_decidable_eq Task) -> SProp) :
  (forall pR pL, PdFPRel Task pR pL -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall pR, PR pR) (forall pL, PL pL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H _ _ (pd_fp_export_certificate Task pL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H _ _ (pd_fp_import_certificate Task pR)) (HL _)).
Qed.

Lemma bbf_reflexive_task_priorities_rel (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : I.Prosa_Model_Priority_Definitions_FP_policy Task (pd_decidable_eq Task)) :
  PdFPRel Task pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.reflexive_task_priorities Task pR)
    (I.Prosa_Model_Priority_Definitions_reflexive_task_priorities Task (pd_decidable_eq Task) pL).
Proof.
  intro HR.
  unfold prosa.model.priority.definitions.reflexive_task_priorities,
    I.Prosa_Model_Priority_Definitions_reflexive_task_priorities.
  apply prop_sprop_rel_intro.
  - intros H x. exact (prop_to_sprop _ _
      (pd_bool_truth_correspondence _ _ (HR x x)) (H x)).
  - intro H. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _
      (pd_bool_truth_correspondence _ _ (HR x x)) (H x)).
Qed.

Lemma bbf_transitive_task_priorities_rel (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : I.Prosa_Model_Priority_Definitions_FP_policy Task (pd_decidable_eq Task)) :
  PdFPRel Task pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.transitive_task_priorities Task pR)
    (I.Prosa_Model_Priority_Definitions_transitive_task_priorities Task (pd_decidable_eq Task) pL).
Proof.
  intro HR.
  unfold prosa.model.priority.definitions.transitive_task_priorities,
    I.Prosa_Model_Priority_Definitions_transitive_task_priorities.
  apply prop_sprop_rel_intro.
  - intros H y x z Hxy Hyz.
    apply (prop_to_sprop _ _ (pd_bool_truth_correspondence _ _ (HR x z))).
    apply (H y x z).
    + exact (sprop_to_prop _ _ (pd_bool_truth_correspondence _ _ (HR x y)) Hxy).
    + exact (sprop_to_prop _ _ (pd_bool_truth_correspondence _ _ (HR y z)) Hyz).
  - intro H. apply strictly_inhabits. intros y x z Hxy Hyz.
    apply (sprop_to_prop _ _ (pd_bool_truth_correspondence _ _ (HR x z))).
    apply (H y x z).
    + exact (prop_to_sprop _ _ (pd_bool_truth_correspondence _ _ (HR x y)) Hxy).
    + exact (prop_to_sprop _ _ (pd_bool_truth_correspondence _ _ (HR y z)) Hyz).
Qed.

Lemma bbf_fp_to_jlfp_rel (Job Task : eqType)
    (jtR : prosa.model.task.concept.JobTask Job Task)
    (jtL : I.Prosa_Model_Task_Concept_JobTask Job (pd_decidable_eq Job) Task (pd_decidable_eq Task))
    (Hjt : forall j : Job, Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job (pd_decidable_eq Job) Task (pd_decidable_eq Task) jtL j))
    fpR fpL :
  PdFPRel Task fpR fpL ->
  PdJLFPRel Job (@prosa.model.priority.coercion.FP_to_JLFP Job Task jtR fpR)
    (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job (pd_decidable_eq Job) Task (pd_decidable_eq Task) jtL fpL).
Proof.
  intros Hfp x y.
  refine (bbf_transport (fun v => PdBoolRel _
    (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task (pd_decidable_eq Task) fpL v
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job (pd_decidable_eq Job) Task (pd_decidable_eq Task) jtL y))) _ _ (Hjt x) _).
  refine (bbf_transport (fun v => PdBoolRel _
    (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task (pd_decidable_eq Task) fpL
      (@prosa.model.task.concept.job_task Job Task jtR x) v)) _ _ (Hjt y) _).
  exact (Hfp _ _).
Qed.

(** ** Covers *)

Definition bbf_fun1_to_target (fR : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun xL => sub_nat_to_imported (fR (sub_nat_to_rocq xL)).
Definition bbf_fun1_to_source (fL : Lean.Nat -> Lean.Nat) : nat -> nat :=
  fun xR => sub_nat_to_rocq (fL (sub_nat_to_imported xR)).

Lemma bbf_fun1_to_target_rel fR : JSI.SvcNatFunRel fR (bbf_fun1_to_target fR).
Proof.
  intros xR xL Hx. unfold bbf_fun1_to_target.
  rewrite (arta_nat_input _ _ Hx). exact (sub_nat_rel_canonical _).
Qed.

Lemma bbf_fun1_to_source_rel fL : JSI.SvcNatFunRel (bbf_fun1_to_source fL) fL.
Proof. intros xR xL Hx. destruct Hx. exact (sub_nat_imported_roundtrip _). Qed.

Lemma bbf_forall_fun1 (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, JSI.SvcNatFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  exact (arta_forall_cover _ _ JSI.SvcNatFunRel bbf_fun1_to_target bbf_fun1_to_source
    bbf_fun1_to_target_rel bbf_fun1_to_source_rel PR PL).
Qed.

Definition BbfSbfRel (sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction)
    (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) : SProp :=
  PC.PredFunctionRel sR (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL).

Definition bbf_sbf_to_target (fR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction) :
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction :=
  I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
    (fun dL => sub_nat_to_imported (fR (sub_nat_to_rocq dL))).
Definition bbf_sbf_to_source (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :
    prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction :=
  ((fun dR => sub_nat_to_rocq
    (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL (sub_nat_to_imported dR)))
    : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction).

Lemma bbf_forall_sbf (PR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction -> Prop)
    (PL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> SProp) :
  (forall sR sL, BbfSbfRel sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  apply (arta_forall_cover _ _ BbfSbfRel bbf_sbf_to_target bbf_sbf_to_source).
  - intros fR nR nL Hn. unfold BbfSbfRel, bbf_sbf_to_target. cbn.
    rewrite (arta_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
  - intros sL nR nL Hn. destruct Hn. exact (sub_nat_imported_roundtrip _).
Qed.

Section BoundedBiFp.
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

  Lemma bbf_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (arta_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma bbf_valid_job_costs_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (bbf_task_cost_of_job_related j))).
  Qed.

  Lemma bbf_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
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

  Definition BbfMaxArrivalsRel (maR : prosa.model.task.arrival.curves.MaxArrivals Task)
      (maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT) : SProp :=
    forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
      SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).

  Lemma bbf_forall_ma (PR : prosa.model.task.arrival.curves.MaxArrivals Task -> Prop)
      (PL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT -> SProp) :
    (forall maR maL, BbfMaxArrivalsRel maR maL -> PropSPropRel (PR maR) (PL maL)) ->
    PropSPropRel (forall m, PR m) (forall m, PL m).
  Proof.
    apply (arta_forall_cover _ _ BbfMaxArrivalsRel
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

  Lemma bbf_forall_jp (PR : PPS.JobPreemptable Job -> Prop)
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

  Lemma bbf_forall_tms (PRm : TPS.TaskMaxNonpreemptiveSegment Task -> Prop)
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

  Lemma bbf_respects_fp_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL)
      arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
      jpR jpL (Hjp : PPC.PpJobPreemptableRel Job jpR jpL)
      jrR jrL (Hjr : RsiJrAt Job PStateR PStateL jaR jaL costR costL sR sL jrR jrL)
      fR fL (Hf : PdFPRel Task fR fL) :
    PropSPropRel (@PDS.respects_FP_policy_at_preemption_point Task Job jtR jaR costR PStateR jpR jrR arrR sR fR)
      (I.Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point
        Task dT Job dJ jtL jaL costL PStateL jpL jrL arrL sL fL).
  Proof.
    unfold PDS.respects_FP_policy_at_preemption_point, PDS.respects_JLDP_policy_at_preemption_point.
    cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point
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
    apply ar_bool_truth_correspondence. cbn.
    exact (sub_imported_eq_trans _ _ _ (Hf _ _)
      (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL)
        _ _ _ _ (Hjt j_hp) (Hjt j))).
  Qed.

  (** *** busy_intervals_are_bounded_rs_fp *)
End BoundedBiFp.
