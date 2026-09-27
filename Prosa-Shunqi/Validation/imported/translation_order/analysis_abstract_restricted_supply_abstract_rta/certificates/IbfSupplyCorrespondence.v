From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IbfSupplySemanticSource.
From prosa Require Import analysis.abstract.definitions model.processor.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRsAbstractRta ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence.

Module I := ImportedRsAbstractRta.
Module S := IbfSupplySemanticSource.IbfSupplySemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.

(** Definition certificates for [analysis/abstract/IBF/supply.v].

    All three definitions condition the abstract interference on the
    presence of supply.  The processor-state pair is related by both
    accepted two-sided relations: the abstract-definitions family's
    [SvcProcessorStateRel] (scheduled/service observations, used by the busy
    interval and completion inside the interference bound) and the supply
    family's [SupplyProcessorStateRel] (supply observations, used by
    [has_supply]); schedules are related through each.  [has_supply] is
    related by the accepted supply certificate, conditional interference, its
    cumulative sum and the conditional interference bound by the accepted
    abstract-definitions certificates, and the relative-arrival parameter by
    the accepted abstract-RTA definition certificate.  Nothing is assumed
    about the definitions; no source or target theorem is used. *)

Section IbfSupply.
  Context (Job : eqType).
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable Rsvc : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Variable Rsup : SUP.SupplyProcessorStateRel Job PStateR PStateL.
  Variable sR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis HsSvc : SSO.SvcScheduleRel Job PStateR PStateL Rsvc sR sL.
  Hypothesis HsSup : SUP.SupplyScheduleRel Job PStateR PStateL Rsup sR sL.

  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
  Hypothesis Hinter : AdInterferenceRel Job interR interL.

  Lemma ibfs_supply_pred_rel :
    AdBoolPredRel Job (fun _ t => @prosa.model.processor.supply.has_supply Job PStateR sR t)
      (fun _ tL => I.Prosa_Model_Processor_Supply_has_supply Job dJ PStateL sL tL).
  Proof.
    intros j t.
    exact (has_supply_correspondence Job PStateR PStateL Rsup sR sL HsSup t _ (sub_nat_rel_canonical t)).
  Qed.

  Theorem intra_interference_correspondence (j : Job) tR tL :
    SubNatRel tR tL ->
    AdBoolRel (@S.intra_interference Job PStateR sR interR j tR)
      (I.Prosa_Analysis_Abstract_IBF_Supply_intra_interference Job dJ PStateL sL interL j tL).
  Proof.
    intro Ht. unfold S.intra_interference.
    cbn [I.Prosa_Analysis_Abstract_IBF_Supply_intra_interference].
    exact (cond_interference_correspondence_general Job interR interL _ _ j tR tL Hinter
      ibfs_supply_pred_rel Ht).
  Qed.

  Theorem cumul_intra_interference_correspondence (j : Job) t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@S.cumul_intra_interference Job PStateR sR interR j t1R t2R)
      (I.Prosa_Analysis_Abstract_IBF_Supply_cumul_intra_interference Job dJ PStateL sL interL j t1L t2L).
  Proof.
    intros H1 H2. unfold S.cumul_intra_interference.
    cbn [I.Prosa_Analysis_Abstract_IBF_Supply_cumul_intra_interference].
    exact (cumul_cond_interference_correspondence Job interR interL Hinter _ _ ibfs_supply_pred_rel
      j t1R t2R t1L t2L H1 H2).
  Qed.

  Variable Task : eqType.
  Let dT := ad_decidable_eq Task.
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
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
  Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable IBFR : nat -> nat -> nat.
  Variable IBFL : Lean.Nat -> Lean.Nat -> Lean.Nat.
  Hypothesis HIBF : ArtaFunRel IBFR IBFL.

  Theorem intra_interference_is_bounded_by_correspondence (tsk : Task) :
    PropSPropRel
      (@S.intra_interference_is_bounded_by Job Task jtR jaR costR PStateR arrR sR tsk interR workloadR IBFR)
      (I.Prosa_Analysis_Abstract_IBF_Supply_intra_interference_is_bounded_by Job dJ Task dT jtL jaL costL
        PStateL arrL sL tsk interL workloadL IBFL).
  Proof.
    unfold S.intra_interference_is_bounded_by.
    cbn [I.Prosa_Analysis_Abstract_IBF_Supply_intra_interference_is_bounded_by].
    refine (ad_cond_interference_bounded_correspondence Job PStateR PStateL Rsvc sR sL HsSvc jaR jaL Hja
      costR costL Hcost interR interL Hinter workloadR workloadL Hworkload arrR arrL Harr Task
      jtR jtL Hjt tsk IBFR IBFL HIBF _ _ _ _ _ ibfs_supply_pred_rel).
    intros j xR xL Hx.
    exact (relative_arrival_time_of_job_is_A_correspondence Job PStateR PStateL Rsvc jaR jaL Hja
      costR costL Hcost sR sL HsSvc interR interL Hinter workloadR workloadL Hworkload j xR xL Hx).
  Qed.
End IbfSupply.
