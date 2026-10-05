From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.spin.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSpinFull.

(** These checks bind the certificate to the compiled official source and
    imported Lean artifact. They are separate from semantic proofs. *)
Check (@prosa.model.processor.spin.processor_state :
  forall Job : prosa.behavior.job.JobType, Type).
Check (@prosa.model.processor.spin.spin_scheduled_on :
  forall (Job : prosa.behavior.job.JobType) (_ : Job)
    (_ : @prosa.model.processor.spin.processor_state Job) (_ : unit), bool).
Check (@prosa.model.processor.spin.spin_supply_on :
  forall (Job : prosa.behavior.job.JobType)
    (_ : @prosa.model.processor.spin.processor_state Job) (_ : unit),
    prosa.behavior.job.work).
Check (@prosa.model.processor.spin.spin_service_on :
  forall (Job : prosa.behavior.job.JobType) (_ : Job)
    (_ : @prosa.model.processor.spin.processor_state Job) (_ : unit),
    prosa.behavior.job.work).
Check (@prosa.model.processor.spin.pstate_instance :
  forall Job : prosa.behavior.job.JobType,
    prosa.behavior.schedule.ProcessorState Job).

Check (ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state :
  forall Job : ImportedSpinFull.Prosa_Behavior_Job_JobType, Type).
Check (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_scheduled_on :
  forall (Job : ImportedSpinFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedSpinFull.DecidableEq Job) (_ : Job)
    (_ : ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state Job)
    (_ : ImportedSpinFull.Unit), ImportedSpinFull.Bool).
Check (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_supply_on :
  forall (Job : ImportedSpinFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedSpinFull.DecidableEq Job)
    (_ : ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state Job)
    (_ : ImportedSpinFull.Unit), ImportedSpinFull.Prosa_Behavior_Job_work).
Check (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_service_on :
  forall (Job : ImportedSpinFull.Prosa_Behavior_Job_JobType)
    (_ : ImportedSpinFull.DecidableEq Job) (_ : Job)
    (_ : ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state Job)
    (_ : ImportedSpinFull.Unit), ImportedSpinFull.Prosa_Behavior_Job_work).
Check (ImportedSpinFull.Prosa_Model_Processor_Spin_pstate_instance :
  forall (Job : ImportedSpinFull.Prosa_Behavior_Job_JobType)
    (deq : ImportedSpinFull.DecidableEq Job),
    ImportedSpinFull.Prosa_Behavior_Schedule_ProcessorState_inst2 Job deq).
