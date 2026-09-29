From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IbfSupplyTaskSemanticSource.
From prosa Require Import analysis.abstract.definitions model.processor.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBoundedBiElf ImportedSubadditivity.
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
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations 
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence 
  IbfTaskHelpers.

Module I := ImportedBoundedBiElf.
Module S := IbfSupplyTaskSemanticSource.IbfSupplyTaskSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module IT := FoundationCertificates.IbfTaskHelpers.

(** Definition certificates for [analysis/abstract/IBF/supply_task.v].

    Source side: the extracted byte-identical definition blocks; target side:
    the compiled Lean definitions.  The processor-state pair is related by
    both accepted two-sided relations: the abstract-definitions family's
    [SvcProcessorStateRel] (used by [nonself] and, inside the interference
    bound, by the busy interval and completion) and the supply family's
    [SupplyProcessorStateRel] (used by [has_supply]); schedules are related
    through each.  [nonself] is related by the accepted IBF/task definition
    certificate, [has_supply] by the accepted supply certificate, conditional
    interference and the conditional interference bound by the accepted
    abstract-definitions certificates, and the relative-arrival parameter by
    the accepted abstract-RTA definition certificate.  No source or target
    theorem is used. *)

Section IbfSupplyTask.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable Rsvc : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Variable Rsup : SUP.SupplyProcessorStateRel Job PStateR PStateL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
  Variable sR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis HsSvc : SSO.SvcScheduleRel Job PStateR PStateL Rsvc sR sL.
  Hypothesis HsSup : SUP.SupplyScheduleRel Job PStateR PStateL Rsup sR sL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Theorem nonself_intra_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    AdBoolRel (@S.nonself_intra Job Task jtR PStateR arrR sR j tR)
      (I.Prosa_Analysis_Abstract_IBF_SupplyTask_nonself_intra Job dJ Task dT jtL PStateL arrL sL j tL).
  Proof.
    intro Ht. unfold S.nonself_intra.
    cbn [I.Prosa_Analysis_Abstract_IBF_SupplyTask_nonself_intra].
    apply ad_bool_and_related.
    - exact (IT.nonself_correspondence Task Job PStateR PStateL Rsvc jtR jtL Hjt sR sL HsSvc arrR arrL Harr j tR tL Ht).
    - exact (has_supply_correspondence Job PStateR PStateL Rsup sR sL HsSup tR tL Ht).
  Qed.

  Lemma ibst_nonself_intra_pred :
    AdBoolPredRel Job (@S.nonself_intra Job Task jtR PStateR arrR sR)
      (I.Prosa_Analysis_Abstract_IBF_SupplyTask_nonself_intra Job dJ Task dT jtL PStateL arrL sL).
  Proof. intros j t. exact (nonself_intra_correspondence j t _ (sub_nat_rel_canonical t)). Qed.

  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
  Hypothesis Hinter : AdInterferenceRel Job interR interL.

  Theorem task_intra_interference_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    AdBoolRel (@S.task_intra_interference Job Task jtR PStateR arrR sR interR j tR)
      (I.Prosa_Analysis_Abstract_IBF_SupplyTask_task_intra_interference Job dJ Task dT jtL PStateL arrL sL
        interL j tL).
  Proof.
    intro Ht. unfold S.task_intra_interference.
    cbn [I.Prosa_Analysis_Abstract_IBF_SupplyTask_task_intra_interference].
    exact (cond_interference_correspondence_general Job interR interL _ _ j tR tL Hinter ibst_nonself_intra_pred Ht).
  Qed.

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
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
  Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.
  Variable IBFR : nat -> nat -> nat.
  Variable IBFL : Lean.Nat -> Lean.Nat -> Lean.Nat.
  Hypothesis HIBF : ArtaFunRel IBFR IBFL.

  Theorem task_intra_interference_is_bounded_by_correspondence (tsk : Task) :
    PropSPropRel
      (@S.task_intra_interference_is_bounded_by Job Task jtR jaR costR PStateR arrR sR tsk interR workloadR IBFR)
      (I.Prosa_Analysis_Abstract_IBF_SupplyTask_task_intra_interference_is_bounded_by Job dJ Task dT jtL jaL
        costL PStateL arrL sL tsk interL workloadL IBFL).
  Proof.
    unfold S.task_intra_interference_is_bounded_by.
    cbn [I.Prosa_Analysis_Abstract_IBF_SupplyTask_task_intra_interference_is_bounded_by].
    refine (ad_cond_interference_bounded_correspondence Job PStateR PStateL Rsvc sR sL HsSvc jaR jaL Hja
      costR costL Hcost interR interL Hinter workloadR workloadL Hworkload arrR arrL Harr Task
      jtR jtL Hjt tsk IBFR IBFL HIBF _ _ _ _ _ ibst_nonself_intra_pred).
    intros j xR xL Hx.
    exact (relative_arrival_time_of_job_is_A_correspondence Job PStateR PStateL Rsvc jaR jaL Hja
      costR costL Hcost sR sL HsSvc interR interL Hinter workloadR workloadL Hworkload j xR xL Hx).
  Qed.
End IbfSupplyTask.
