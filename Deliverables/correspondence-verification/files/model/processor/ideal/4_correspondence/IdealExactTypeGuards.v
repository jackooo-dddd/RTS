From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.ideal.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdeal.

Check (@prosa.model.processor.ideal.processor_state :
  forall Job : prosa.behavior.job.JobType,
    prosa.behavior.schedule.ProcessorState Job).
Check (ImportedIdeal.Prosa_Model_Processor_Ideal_processor_state :
  forall (Job : ImportedIdeal.Prosa_Behavior_Job_JobType)
    (deq : ImportedIdeal.DecidableEq Job),
    ImportedIdeal.Prosa_Behavior_Schedule_ProcessorState_inst2 Job deq).

Check (@prosa.model.processor.ideal.ideal_is_idle :
  forall (Job : prosa.behavior.job.JobType),
    prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job) ->
    prosa.behavior.time.instant -> bool).
Check (ImportedIdeal.Prosa_Model_Processor_Ideal_ideal_is_idle :
  forall (Job : ImportedIdeal.Prosa_Behavior_Job_JobType)
    (deq : ImportedIdeal.DecidableEq Job),
    ImportedIdeal.Prosa_Behavior_Schedule_schedule_inst4 Job deq
      (ImportedIdeal.Prosa_Model_Processor_Ideal_processor_state Job deq) ->
    ImportedIdeal.Prosa_Behavior_Time_instant -> ImportedIdeal.Bool).
