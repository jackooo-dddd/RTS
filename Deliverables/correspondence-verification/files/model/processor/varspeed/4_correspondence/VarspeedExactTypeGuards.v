From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.varspeed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedVarspeedFull.

(** These checks refer to the compiled patched official source and to the
    actual imported Lean artifact. The compatibility patch changes only the
    proof scripts of the two Program obligations. *)
Check (@prosa.model.processor.varspeed.processor_state :
  prosa.behavior.job.JobType -> Type).
Check (@prosa.model.processor.varspeed.varspeed_scheduled_on :
  forall (Job : prosa.behavior.job.JobType), Job ->
    @prosa.model.processor.varspeed.processor_state Job -> unit -> bool).
Check (@prosa.model.processor.varspeed.varspeed_supply_on :
  forall (Job : prosa.behavior.job.JobType),
    @prosa.model.processor.varspeed.processor_state Job -> unit ->
    prosa.behavior.job.work).
Check (@prosa.model.processor.varspeed.varspeed_service_on :
  forall (Job : prosa.behavior.job.JobType), Job ->
    @prosa.model.processor.varspeed.processor_state Job -> unit ->
    prosa.behavior.job.work).
Check (@prosa.model.processor.varspeed.pstate_instance :
  forall Job : prosa.behavior.job.JobType,
    prosa.behavior.schedule.ProcessorState Job).

Check (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state :
  ImportedVarspeedFull.Prosa_Behavior_Job_JobType -> Type).
Check (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state_Idle :
  forall Job : ImportedVarspeedFull.Prosa_Behavior_Job_JobType,
    Lean.Nat ->
    ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state Job).
Check (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state_Progress :
  forall Job : ImportedVarspeedFull.Prosa_Behavior_Job_JobType,
    Job -> Lean.Nat ->
    ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state Job).
Check (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_scheduled_on :
  forall (Job : ImportedVarspeedFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedVarspeedFull.DecidableEq Job) (_ : Job)
    (_ : ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state Job)
    (_ : ImportedVarspeedFull.Unit), ImportedVarspeedFull.Bool).
Check (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_supply_on :
  forall (Job : ImportedVarspeedFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedVarspeedFull.DecidableEq Job)
    (_ : ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state Job)
    (_ : ImportedVarspeedFull.Unit), ImportedVarspeedFull.Prosa_Behavior_Job_work).
Check (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_service_on :
  forall (Job : ImportedVarspeedFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedVarspeedFull.DecidableEq Job) (_ : Job)
    (_ : ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state Job)
    (_ : ImportedVarspeedFull.Unit), ImportedVarspeedFull.Prosa_Behavior_Job_work).
Check (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_pstate_instance :
  forall (Job : ImportedVarspeedFull.Prosa_Behavior_Job_JobType)
    (deq : ImportedVarspeedFull.DecidableEq Job),
    ImportedVarspeedFull.Prosa_Behavior_Schedule_ProcessorState_inst2 Job deq).
