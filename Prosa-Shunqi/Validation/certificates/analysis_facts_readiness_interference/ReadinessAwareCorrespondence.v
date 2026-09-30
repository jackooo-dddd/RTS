From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import ReadinessAwareSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsReadinessInterference ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations
  JitterSvcJobOperations PreemptionParameterCorrespondence ServiceInversionPredCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations
  AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations
  AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations
  ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers AbstractDefinitionsBusyInterval PriorityBaseAdapter
  ReadinessInterferenceCorrespondence.

Module I := ImportedFactsReadinessInterference.
Module S := ReadinessAwareSemanticSource.ReadinessAwareSemanticSource.
Module JS := FoundationCertificates.JitterSvcScheduleOperations.
Module SS := FoundationCertificates.ServiceScheduleOperations.

(** Definition certificates for
    [analysis/definitions/service_inversion/readiness_aware.v]: for related
    processor states and schedules (the accepted two-sided Service relations
    of both certificate generations, over the same state pair), job-arrival,
    job-cost, readiness, JLFP, interference and interfering-workload instances
    and arrival sequences (the accepted relations, each with two-way totals),
    the three extracted source definitions and the compiled Lean definitions
    are related; jobs are an identity carrier, instants and durations are
    related by [SubNatRel].  The readiness-aware service inversion is the
    conjunction of the accepted [some_hep_job_ready] and readiness-oblivious
    [service_inversion] relations; the JLDP relation of the coerced policy is
    the JLFP relation itself. *)

Section ReadinessAware.
  Context (Job : eqType).
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable Rs : SS.SvcProcessorStateRel Job PStateR PStateL.
  Variable Rj : JS.SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis HschedS : SS.SvcScheduleRel Job PStateR PStateL Rs schedR schedL.
  Hypothesis HschedJ : JS.SvcScheduleRel Job PStateR PStateL Rj schedR schedL.
  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Harrival : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ arrivalL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).
  Variable readyR : @prosa.behavior.ready.JobReady Job PStateR costR arrivalR.
  Variable readyL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL arrivalL.
  Hypothesis Hready : forall j tR tL, SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR readyR schedR j tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL arrivalL readyL schedL j tL).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable jlfpR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable jlfpL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hjlfp : PdJLFPRel Job jlfpR jlfpL.

  Lemma ra_jldp_related : forall tR tL, SubNatRel tR tL -> forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job_at Job
        (@prosa.model.priority.coercion.JLFP_to_JLDP Job jlfpR) tR x y)
      (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ
        (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ jlfpL) tL x y).
  Proof. intros tR tL Ht x y. exact (Hjlfp x y). Qed.

  Theorem service_inversion_correspondence (j : Job) tR tL : SubNatRel tR tL ->
    ArBoolRel (@S.service_inversion Job arrivalR costR PStateR readyR arrR schedR jlfpR j tR)
      (I.Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion
        Job dJ arrivalL costL PStateL readyL arrL schedL jlfpL j tL).
  Proof.
    intro Ht. unfold S.service_inversion.
    cbn [I.Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion].
    apply ar_bool_and_related.
    - exact (some_hep_job_ready_correspondence Job PStateR PStateL schedR schedL
        arrivalR arrivalL costR costL readyR readyL Hready arrR arrL Harr
        jlfpR jlfpL Hjlfp j tR tL Ht).
    - exact (ServiceInversionPredCorrespondence.service_inversion_correspondence Job PStateR PStateL Rj
        schedR schedL HschedJ arrR arrL Harr _ _ ra_jldp_related j tR tL Ht).
  Qed.

  Theorem cumulative_service_inversion_correspondence (j : Job) t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@S.cumulative_service_inversion Job arrivalR costR PStateR readyR arrR schedR jlfpR j t1R t2R)
      (I.Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_cumulative_service_inversion
        Job dJ arrivalL costL PStateL readyL arrL schedL jlfpL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => nat_of_bool (@S.service_inversion Job arrivalR costR PStateR readyR arrR schedR jlfpR j t))
      (fun t => I.Bool_toNat (I.Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion
        Job dJ arrivalL costL PStateL readyL arrL schedL jlfpL j t))
      Ht1 Ht2
      (fun a b Hab => ad_bool_to_nat_related _ _ (service_inversion_correspondence j a b Hab)).
    change (SubNatRel (@S.cumulative_service_inversion Job arrivalR costR PStateR readyR arrR schedR jlfpR j t1R t2R)
      (I.Prosa_Validation_ReadinessAwareInterface_cumulativeServiceInversionProjection
        Job dJ arrivalL costL PStateL readyL arrL schedL jlfpL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
  Hypothesis Hinter : AdInterferenceRel Job interR interL.
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
  Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.
  Variable BR : nat -> nat.
  Variable BL : Lean.Nat -> Lean.Nat.
  Hypothesis HB : SubNatFunRel BR BL.

  Theorem service_inversion_is_bounded_correspondence :
    PropSPropRel
      (@S.service_inversion_is_bounded Job arrivalR costR PStateR readyR arrR schedR jlfpR interR workloadR BR)
      (I.Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion_is_bounded
        Job dJ arrivalL costL PStateL readyL arrL schedL jlfpL interL workloadL BL).
  Proof.
    unfold S.service_inversion_is_bounded.
    cbn [I.Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion_is_bounded].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence.
    - exact (ad_busy_interval_prefix_correspondence Job PStateR PStateL Rs schedR schedL HschedS
        arrivalR arrivalL Harrival costR costL Hcost interR interL Hinter workloadR workloadL Hworkload
        j t1R t2R t1L t2L Ht1 Ht2).
    - exact (sub_nat_le_correspondence _ _ _ _
        (cumulative_service_inversion_correspondence j _ _ _ _ Ht1 Ht2)
        (HB _ _ (svc_target_sub_related _ _ _ _ (Harrival j) Ht1))).
  Qed.
End ReadinessAware.
