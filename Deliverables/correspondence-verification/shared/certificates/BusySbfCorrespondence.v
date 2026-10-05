From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.abstract.restricted_supply.busy_sbf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusySbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  PredCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsClasses
  AbstractDefinitionsTaskOperations AbstractDefinitionsBusyInterval.

(** Correspondence for [analysis/abstract/restricted_supply/busy_sbf.v].
    Both definitions instantiate the accepted [pred_sbf_respected] /
    [valid_pred_sbf] certificates (whose predicate parameter is related
    pointwise) with the source-local predicate
    [fun j t1 t2 => job_of_task tsk j /\ busy_interval_prefix sched j t1 t2];
    that predicate relation is proved here from the accepted
    [job_of_task] and [busy_interval_prefix] certificates, not assumed. *)

Section BusySbf.
  Context (Task Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState Job (ad_decidable_eq Job).

  (** Input representation relations for the processor state and schedule:
      the supply observation (sbf/pred chain) and the scheduled/service
      observation (abstract/definitions chain) of the same state pair. *)
  Variable Rsupply : SupplyProcessorStateRel Job PStateR PStateL.
  Variable Rservice : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedBusySbf.Prosa_Behavior_Schedule_schedule
    Job (ad_decidable_eq Job) PStateL.
  Hypothesis HschedSupply : SupplyScheduleRel Job PStateR PStateL Rsupply schedR schedL.
  Hypothesis HschedService : SvcScheduleRel Job PStateR PStateL Rservice schedR schedL.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : ImportedBusySbf.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ad_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedBusySbf.Prosa_Behavior_Job_JobArrival Job (ad_decidable_eq Job).
  Hypothesis Harrival : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (ImportedBusySbf.Prosa_Behavior_Job_JobArrival_job_arrival Job
        (ad_decidable_eq Job) arrivalL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedBusySbf.Prosa_Behavior_Job_JobCost Job (ad_decidable_eq Job).
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (ImportedBusySbf.Prosa_Behavior_Job_JobCost_job_cost Job
        (ad_decidable_eq Job) costL j).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : ImportedBusySbf.Prosa_Model_Task_Concept_JobTask
    Job (ad_decidable_eq Job) Task (ad_decidable_eq Task).
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL : ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_Interference
    Job (ad_decidable_eq Job).
  Hypothesis Hinter : AdInterferenceRel Job interR interL.
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL :
    ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
      Job (ad_decidable_eq Job).
  Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.

  Variable tsk : Task.

  Definition busy_predR (j : Job) (t1 t2 : nat) : Prop :=
    is_true (@prosa.model.task.concept.job_of_task Job Task jtR tsk j) /\
    @prosa.analysis.abstract.definitions.busy_interval_prefix
      Job arrivalR costR PStateR schedR interR workloadR j t1 t2.

  Definition busy_predL (j : Job) (t1 t2 : Lean.Nat) : SProp :=
    And
      (Lean.eq (ImportedBusySbf.Prosa_Model_Task_Concept_job_of_task
        Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) jtL tsk j)
        ImportedBusySbf.Bool_true)
      (ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_busy_interval_prefix
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL schedL j t1 t2).

  Lemma busy_pred_related : PredPredicateRel Job busy_predR busy_predL.
  Proof.
    intros j t1R t1L t2R t2L Ht1 Ht2.
    apply ar_and_correspondence.
    - exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt)).
    - exact (ad_busy_interval_prefix_correspondence Job PStateR PStateL Rservice
        schedR schedL HschedService arrivalR arrivalL Harrival costR costL Hcost
        interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L Ht1 Ht2).
  Qed.

  Variable fR : nat -> nat.
  Variable fL : Lean.Nat -> Lean.Nat.
  Hypothesis Hf : PredFunctionRel fR fL.

  Theorem sbf_respected_in_busy_interval_correspondence :
    PropSPropRel
      (@sbf_respected_in_busy_interval Task Job arrivalR costR jtR PStateR
        arrR schedR tsk interR workloadR fR)
      (ImportedBusySbf.Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_sbf_respected_in_busy_interval
        Task (ad_decidable_eq Task) Job (ad_decidable_eq Job) arrivalL costL jtL
        PStateL arrL schedL tsk interL workloadL fL).
  Proof.
    exact (pred_sbf_respected_correspondence Job PStateR PStateL Rsupply
      schedR schedL HschedSupply arrR arrL Harr busy_predR busy_predL
      busy_pred_related fR fL Hf).
  Qed.

  Theorem valid_busy_sbf_correspondence :
    PropSPropRel
      (@valid_busy_sbf Task Job arrivalR costR jtR PStateR
        arrR schedR tsk interR workloadR fR)
      (ImportedBusySbf.Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_valid_busy_sbf
        Task (ad_decidable_eq Task) Job (ad_decidable_eq Job) arrivalL costL jtL
        PStateL arrL schedL tsk interL workloadL fL).
  Proof.
    exact (pred_valid_pred_sbf_correspondence Job PStateR PStateL Rsupply
      schedR schedL HschedSupply arrR arrL Harr busy_predR busy_predL
      busy_pred_related fR fL Hf).
  Qed.
End BusySbf.

Print Assumptions sbf_respected_in_busy_interval_correspondence.
Print Assumptions valid_busy_sbf_correspondence.
