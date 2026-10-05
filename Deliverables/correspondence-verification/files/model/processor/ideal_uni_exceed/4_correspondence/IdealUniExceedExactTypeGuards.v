From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.ideal_uni_exceed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealUniExceed.

(** These checks elaborate the public source types and the actual imported
    compiled Lean declarations; neither side is a hand-written substitute. *)
Check (@prosa.model.processor.ideal_uni_exceed.exceedance_processor_state :
  forall Job : prosa.behavior.job.JobType, Type).
Check (@prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef :
  forall (Job : prosa.behavior.job.JobType)
    (_ _ : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job),
    bool).
Check (@prosa.model.processor.ideal_uni_exceed.eqn_exceedance_processor_state :
  forall Job : prosa.behavior.job.JobType,
    Equality.axiom
      (@prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef Job)).
Check (@prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on :
  forall (Job : prosa.behavior.job.JobType) (_ : Job)
    (_ : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job)
    (_ : unit), bool).
Check (@prosa.model.processor.ideal_uni_exceed.exceedance_supply_on :
  forall (Job : prosa.behavior.job.JobType)
    (_ : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job)
    (_ : unit), prosa.behavior.job.work).
Check (@prosa.model.processor.ideal_uni_exceed.exceedance_service_on :
  forall (Job : prosa.behavior.job.JobType) (_ : Job)
    (_ : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job)
    (_ : unit), prosa.behavior.job.work).
Check (@prosa.model.processor.ideal_uni_exceed.exceedance_proc_state :
  forall Job : prosa.behavior.job.JobType,
    prosa.behavior.schedule.ProcessorState Job).

Check (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state :
  forall Job : ImportedIdealUniExceed.Prosa_Behavior_Job_JobType, Type).
Check (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef :
  forall (Job : ImportedIdealUniExceed.Prosa_Behavior_Job_JobType)
    (_ : ImportedIdealUniExceed.DecidableEq Job)
    (_ _ : ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job),
    ImportedIdealUniExceed.Bool).
Check (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_eqn_exceedance_processor_state :
  forall (Job : ImportedIdealUniExceed.Prosa_Behavior_Job_JobType)
    (deq : ImportedIdealUniExceed.DecidableEq Job)
    (p1 p2 : ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job),
    ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect
      (Lean.eq p1 p2)
      (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef
        Job deq p1 p2)).
Check (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on :
  forall (Job : ImportedIdealUniExceed.Prosa_Behavior_Job_JobType)
    (_ : ImportedIdealUniExceed.DecidableEq Job) (_ : Job)
    (_ : ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job)
    (_ : ImportedIdealUniExceed.Unit), ImportedIdealUniExceed.Bool).
Check (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_supply_on :
  forall (Job : ImportedIdealUniExceed.Prosa_Behavior_Job_JobType)
    (_ : ImportedIdealUniExceed.DecidableEq Job)
    (_ : ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job)
    (_ : ImportedIdealUniExceed.Unit), ImportedIdealUniExceed.Prosa_Behavior_Job_work).
Check (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_service_on :
  forall (Job : ImportedIdealUniExceed.Prosa_Behavior_Job_JobType)
    (_ : ImportedIdealUniExceed.DecidableEq Job) (_ : Job)
    (_ : ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job)
    (_ : ImportedIdealUniExceed.Unit), ImportedIdealUniExceed.Prosa_Behavior_Job_work).
Check (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state :
  forall (Job : ImportedIdealUniExceed.Prosa_Behavior_Job_JobType)
    (deq : ImportedIdealUniExceed.DecidableEq Job),
    ImportedIdealUniExceed.Prosa_Behavior_Schedule_ProcessorState_inst2 Job deq).
