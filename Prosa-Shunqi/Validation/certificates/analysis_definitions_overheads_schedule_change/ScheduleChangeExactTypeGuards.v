From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.definitions.overheads.schedule_change.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduleChange.

Check (@prosa.analysis.definitions.overheads.schedule_change.schedule_change :
  forall Job : prosa.behavior.job.JobType,
    @prosa.behavior.schedule.schedule Job
      (@prosa.model.processor.overheads.processor_state Job) ->
    prosa.behavior.time.instant -> bool).
Check (ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change :
  forall (Job : ImportedScheduleChange.Prosa_Behavior_Job_JobType)
    (deq : ImportedScheduleChange.DecidableEq Job),
    ImportedScheduleChange.Prosa_Behavior_Schedule_schedule_inst4 Job deq
      (ImportedScheduleChange.Prosa_Model_Processor_Overheads_processor_state Job deq) ->
    ImportedScheduleChange.Prosa_Behavior_Time_instant ->
    ImportedScheduleChange.Bool).

Check (@prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes :
  forall Job : prosa.behavior.job.JobType,
    @prosa.behavior.schedule.schedule Job
      (@prosa.model.processor.overheads.processor_state Job) ->
    prosa.behavior.time.instant -> prosa.behavior.time.instant -> nat).
Check (ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes :
  forall (Job : ImportedScheduleChange.Prosa_Behavior_Job_JobType)
    (deq : ImportedScheduleChange.DecidableEq Job),
    ImportedScheduleChange.Prosa_Behavior_Schedule_schedule_inst4 Job deq
      (ImportedScheduleChange.Prosa_Model_Processor_Overheads_processor_state Job deq) ->
    ImportedScheduleChange.Prosa_Behavior_Time_instant ->
    ImportedScheduleChange.Prosa_Behavior_Time_instant ->
    Lean.Nat).

Check (@prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during :
  forall Job : prosa.behavior.job.JobType,
    @prosa.behavior.schedule.schedule Job
      (@prosa.model.processor.overheads.processor_state Job) ->
    prosa.behavior.time.instant -> prosa.behavior.time.instant -> bool).
Check (ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during :
  forall (Job : ImportedScheduleChange.Prosa_Behavior_Job_JobType)
    (deq : ImportedScheduleChange.DecidableEq Job),
    ImportedScheduleChange.Prosa_Behavior_Schedule_schedule_inst4 Job deq
      (ImportedScheduleChange.Prosa_Model_Processor_Overheads_processor_state Job deq) ->
    ImportedScheduleChange.Prosa_Behavior_Time_instant ->
    ImportedScheduleChange.Prosa_Behavior_Time_instant ->
    ImportedScheduleChange.Bool).

Check (@prosa.analysis.definitions.overheads.schedule_change.scheduled_job_invariant :
  forall Job : prosa.behavior.job.JobType,
    @prosa.behavior.schedule.schedule Job
      (@prosa.model.processor.overheads.processor_state Job) ->
    option Job -> prosa.behavior.time.instant ->
    prosa.behavior.time.instant -> bool).
Check (ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant :
  forall (Job : ImportedScheduleChange.Prosa_Behavior_Job_JobType)
    (deq : ImportedScheduleChange.DecidableEq Job),
    ImportedScheduleChange.Prosa_Behavior_Schedule_schedule_inst4 Job deq
      (ImportedScheduleChange.Prosa_Model_Processor_Overheads_processor_state Job deq) ->
    ImportedScheduleChange.Option Job ->
    ImportedScheduleChange.Prosa_Behavior_Time_instant ->
    ImportedScheduleChange.Prosa_Behavior_Time_instant ->
    ImportedScheduleChange.Bool).
