From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.restricted_supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRestrictedSupplyFull.

(** Exact-type checks refer directly to the compiled source and imported
    target declarations. This file is separate from the semantic proofs. *)
Check (@prosa.model.processor.restricted_supply.processor_state :
  forall Job : prosa.behavior.job.JobType, Type).
Check (@prosa.model.processor.restricted_supply.rs_scheduled_on :
  forall (Job : prosa.behavior.job.JobType) (_ : Job)
    (_ : @prosa.model.processor.restricted_supply.processor_state Job), bool).
Check (@prosa.model.processor.restricted_supply.rs_supply_on :
  forall (Job : prosa.behavior.job.JobType)
    (_ : @prosa.model.processor.restricted_supply.processor_state Job),
    prosa.behavior.job.work).
Check (@prosa.model.processor.restricted_supply.rs_service_on :
  forall (Job : prosa.behavior.job.JobType) (_ : Job)
    (_ : @prosa.model.processor.restricted_supply.processor_state Job),
    prosa.behavior.job.work).
Check (@prosa.model.processor.restricted_supply.rs_processor_state :
  forall Job : prosa.behavior.job.JobType,
    prosa.behavior.schedule.ProcessorState Job).

Check (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state :
  forall Job : ImportedRestrictedSupplyFull.Prosa_Behavior_Job_JobType, Type).
Check (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_scheduled_on :
  forall (Job : ImportedRestrictedSupplyFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedRestrictedSupplyFull.DecidableEq Job) (_ : Job)
    (_ : ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state Job),
    ImportedRestrictedSupplyFull.Bool).
Check (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_supply_on :
  forall (Job : ImportedRestrictedSupplyFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedRestrictedSupplyFull.DecidableEq Job)
    (_ : ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state Job),
    ImportedRestrictedSupplyFull.Prosa_Behavior_Job_work).
Check (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_service_on :
  forall (Job : ImportedRestrictedSupplyFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedRestrictedSupplyFull.DecidableEq Job) (_ : Job)
    (_ : ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state Job),
    ImportedRestrictedSupplyFull.Prosa_Behavior_Job_work).
Check (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_processor_state :
  forall (Job : ImportedRestrictedSupplyFull.Prosa_Behavior_Job_JobType)
    (deq : ImportedRestrictedSupplyFull.DecidableEq Job),
    ImportedRestrictedSupplyFull.Prosa_Behavior_Schedule_ProcessorState_inst2 Job deq).
