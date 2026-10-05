From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import BusyPrefixSemanticSource analysis.abstract.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusyPrefix ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  ServiceInversionPredCorrespondence.
From FoundationCertificates Require
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses
  AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations
  AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical
  ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations
  AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers.

Module I := ImportedBusyPrefix.
Module S := BusyPrefixSemanticSource.BusyPrefixSemanticSource.
Module OSS := FoundationCertificates.ServiceScheduleOperations.
Module ADC := FoundationCertificates.AbstractDefinitionsClasses.
Module ADB := FoundationCertificates.AbstractDefinitionsBusyIntervalHelpers.

(** Definition certificates for [analysis/abstract/restricted_supply/busy_prefix.v].

    Both definitions instantiate the accepted [pred_service_inversion_*]
    certificates of the service-inversion family (ArrivalsSeq / JitterSvc),
    whose predicate parameter is related pointwise, with the abstract
    busy-interval prefix [busy_interval_prefix sched].  That predicate
    relation is the accepted abstract [busy_interval_prefix] certificate of
    the abstract-definitions family (Service / AbstractDefinitions); nothing
    is assumed about the predicate.  As in the accepted abstract [busy_sbf]
    certificate, the processor-state pair is related by the accepted
    two-sided relation of each family (both are scheduled/service
    observations of the same state pair), with schedules related through
    each.  The JLFP policy is related pointwise and reaches the JLDP-based
    predicates through [JLFP_to_JLDP] on both sides.  No source or target
    theorem is used. *)

Section BusyPrefix.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.

  Variable Rsvc : SvcProcessorStateRel Job PStateR PStateL.
  Variable Rabs : OSS.SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis HschedSvc : SvcScheduleRel Job PStateR PStateL Rsvc schedR schedL.
  Hypothesis HschedAbs : OSS.SvcScheduleRel Job PStateR PStateL Rabs schedR schedL.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
  Hypothesis Hinter : ADC.AdInterferenceRel Job interR interL.
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
  Hypothesis Hworkload : ADC.AdInterferingWorkloadRel Job workloadR workloadL.

  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Lemma bpfx_busy_prefix_related (j : Job) t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel
      (@prosa.analysis.abstract.definitions.busy_interval_prefix
        Job jaR costR PStateR schedR interR workloadR j t1R t2R)
      (I.Prosa_Analysis_Abstract_Definitions_busy_interval_prefix
        Job dJ interL workloadL jaL costL PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    exact (ADB.ad_busy_interval_prefix_correspondence Job PStateR PStateL Rabs
      schedR schedL HschedAbs jaR jaL Hja costR costL Hcost
      interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L Ht1 Ht2).
  Qed.

  Variable BR : nat -> nat.
  Variable BL : Lean.Nat -> Lean.Nat.
  Hypothesis HB : SvcNatFunRel BR BL.

  Theorem service_inversion_of_job_is_bounded_by_correspondence (j : Job) :
    PropSPropRel
      (@S.service_inversion_of_job_is_bounded_by Job jaR costR PStateR arrR schedR
        interR workloadR pR j BR)
      (I.Prosa_Analysis_Abstract_RestrictedSupply_BusyPrefix_service_inversion_of_job_is_bounded_by
        Job dJ jaL costL PStateL arrL schedL interL workloadL pL j BL).
  Proof.
    unfold S.service_inversion_of_job_is_bounded_by.
    cbn [I.Prosa_Analysis_Abstract_RestrictedSupply_BusyPrefix_service_inversion_of_job_is_bounded_by].
    refine (pred_service_inversion_of_job_is_bounded_by_correspondence Job PStateR PStateL Rsvc
      schedR schedL HschedSvc arrR arrL Harr _ _ _ jaR jaL Hja
      _ _ bpfx_busy_prefix_related j BR BL HB).
    intros tR tL _ x y. exact (Hp x y).
  Qed.

  Theorem service_inversion_is_bounded_by_correspondence (tsk : Task) :
    PropSPropRel
      (@S.service_inversion_is_bounded_by Task Job jtR jaR costR PStateR arrR schedR
        interR workloadR pR tsk BR)
      (I.Prosa_Analysis_Abstract_RestrictedSupply_BusyPrefix_service_inversion_is_bounded_by
        Task dT Job dJ jtL jaL costL PStateL arrL schedL interL workloadL pL tsk BL).
  Proof.
    unfold S.service_inversion_is_bounded_by.
    cbn [I.Prosa_Analysis_Abstract_RestrictedSupply_BusyPrefix_service_inversion_is_bounded_by].
    refine (pred_service_inversion_is_bounded_by_correspondence Task Job jtR jtL Hjt jaR jaL Hja
      costR costL Hcost PStateR PStateL Rsvc schedR schedL HschedSvc arrR arrL Harr
      _ _ _ _ _ bpfx_busy_prefix_related tsk BR BL HB).
    intros tR tL _ x y. exact (Hp x y).
  Qed.
End BusyPrefix.
