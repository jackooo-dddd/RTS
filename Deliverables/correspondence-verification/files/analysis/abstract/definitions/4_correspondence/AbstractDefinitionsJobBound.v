From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.abstract.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAbstractDefinitions ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence AbstractDefinitionsBaseAdapter
  AbstractDefinitionsClasses AbstractDefinitionsOperations
  AbstractDefinitionsTaskOperations AbstractDefinitionsArrivalOperations
  AbstractDefinitionsBusyInterval ServiceBaseAdapter ServiceScheduleOperations.

(** The unconditional bound is definitionally the conditional bound for the
    constant true predicate.  This proof reuses the independently certified
    higher-order conditional interface; neither side's bound is proved true. *)
Section JobBound.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedAbstractDefinitions.Prosa_Behavior_Schedule_ProcessorState Job
      (ad_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedAbstractDefinitions.Prosa_Behavior_Schedule_schedule
    Job (ad_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedAbstractDefinitions.Prosa_Behavior_Job_JobArrival
    Job (ad_decidable_eq Job).
  Hypothesis Harrival : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (ImportedAbstractDefinitions.Prosa_Behavior_Job_JobArrival_job_arrival
        Job (ad_decidable_eq Job) arrivalL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedAbstractDefinitions.Prosa_Behavior_Job_JobCost Job
    (ad_decidable_eq Job).
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (ImportedAbstractDefinitions.Prosa_Behavior_Job_JobCost_job_cost
        Job (ad_decidable_eq Job) costL j).
  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL :
    ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_Interference
      Job (ad_decidable_eq Job).
  Hypothesis Hinter : AdInterferenceRel Job interR interL.
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL :
    ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
      Job (ad_decidable_eq Job).
  Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.
  Variable arrSeqR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrSeqL :
    ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ad_decidable_eq Job).
  Hypothesis HarrSeq : AdArrivalSequenceRel Job arrSeqR arrSeqL.
  Variable Task : eqType.
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL :
    ImportedAbstractDefinitions.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task).
  Hypothesis HjobTask : AdJobTaskRel Job Task jobTaskR jobTaskL.
  Variable tsk : Task.
  Variable IBFR : nat -> nat -> nat.
  Variable IBFL : Lean.Nat -> Lean.Nat -> Lean.Nat.
  Hypothesis HIBF : forall xR xL dR dL,
    SubNatRel xR xL -> SubNatRel dR dL ->
    SubNatRel (IBFR xR dR) (IBFL xL dL).
  Variable ParamSemR : Job -> nat -> Prop.
  Variable ParamSemL : Job -> Lean.Nat -> SProp.
  Hypothesis HParamSem : forall j xR xL,
    SubNatRel xR xL ->
    PropSPropRel (ParamSemR j xR) (ParamSemL j xL).

  Lemma ad_job_interference_bounded_correspondence :
    PropSPropRel
      (@prosa.analysis.abstract.definitions.job_interference_is_bounded_by
        Job Task jobTaskR arrivalR costR PStateR arrSeqR schedR tsk
        interR workloadR IBFR ParamSemR)
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL arrSeqL schedL Task (ad_decidable_eq Task)
        jobTaskL tsk IBFL ParamSemL).
  Proof.
    change (PropSPropRel
      (@prosa.analysis.abstract.definitions.cond_interference_is_bounded_by
        Job Task jobTaskR arrivalR costR PStateR arrSeqR schedR tsk
        interR workloadR IBFR ParamSemR (fun _ _ => true))
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_cond_interference_is_bounded_by
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL arrSeqL schedL Task (ad_decidable_eq Task)
        jobTaskL tsk IBFL ParamSemL
        (fun _ _ => ImportedAbstractDefinitions.Bool_true))).
    apply (@ad_cond_interference_bounded_correspondence
      Job PStateR PStateL R schedR schedL Hsched
      arrivalR arrivalL Harrival costR costL Hcost
      interR interL Hinter workloadR workloadL Hworkload
      arrSeqR arrSeqL HarrSeq Task jobTaskR jobTaskL HjobTask tsk
      IBFR IBFL HIBF ParamSemR ParamSemL HParamSem
      (fun _ _ => true)
      (fun _ _ => ImportedAbstractDefinitions.Bool_true)).
    intros j t. exact (@Lean.eq_refl _ _).
  Qed.
End JobBound.

Print Assumptions ad_job_interference_bounded_correspondence.
