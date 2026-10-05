From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.overheads.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheads.

(** These guards elaborate the official Rocq names and the actual imported
    compiled Lean names in the same Rocq environment as the certificates. *)
Check (@prosa.model.processor.overheads.proc_state :
  prosa.behavior.job.JobType -> Type).
Check (@prosa.model.processor.overheads.overheads_scheduled_on :
  forall (Job : prosa.behavior.job.JobType), Job ->
    prosa.model.processor.overheads.proc_state Job -> unit -> bool).
Check (@prosa.model.processor.overheads.overheads_supply_on :
  forall (Job : prosa.behavior.job.JobType),
    prosa.model.processor.overheads.proc_state Job -> unit ->
    prosa.behavior.job.work).
Check (@prosa.model.processor.overheads.overheads_service_on :
  forall (Job : prosa.behavior.job.JobType), Job ->
    prosa.model.processor.overheads.proc_state Job -> unit ->
    prosa.behavior.job.work).
Check (@prosa.model.processor.overheads.processor_state :
  forall Job : prosa.behavior.job.JobType,
    prosa.behavior.schedule.ProcessorState Job).

Check (ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state :
  ImportedOverheads.Prosa_Behavior_Job_JobType -> Type).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_scheduled_on :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType),
    ImportedOverheads.DecidableEq Job -> Job ->
    ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state Job ->
    ImportedOverheads.Unit -> ImportedOverheads.Bool).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_supply_on :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType),
    ImportedOverheads.DecidableEq Job ->
    ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state Job ->
    ImportedOverheads.Unit -> ImportedOverheads.Prosa_Behavior_Job_work).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_service_on :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType),
    ImportedOverheads.DecidableEq Job -> Job ->
    ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state Job ->
    ImportedOverheads.Unit -> ImportedOverheads.Prosa_Behavior_Job_work).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_processor_state :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    ImportedOverheads.Prosa_Behavior_Schedule_ProcessorState_inst2 Job deq).

Definition OvhSourceScheduleType (Job : prosa.behavior.job.JobType) : Type :=
  @prosa.behavior.schedule.schedule Job
    (@prosa.model.processor.overheads.processor_state Job).

Check (@prosa.model.processor.overheads.scheduled_job :
  forall Job : prosa.behavior.job.JobType,
    OvhSourceScheduleType Job -> prosa.behavior.time.instant -> option Job).
Check (@prosa.model.processor.overheads.is_progress :
  forall Job : prosa.behavior.job.JobType,
    OvhSourceScheduleType Job -> prosa.behavior.time.instant -> bool).
Check (@prosa.model.processor.overheads.is_context_switch :
  forall Job : prosa.behavior.job.JobType,
    OvhSourceScheduleType Job -> prosa.behavior.time.instant -> bool).
Check (@prosa.model.processor.overheads.is_dispatch :
  forall Job : prosa.behavior.job.JobType,
    OvhSourceScheduleType Job -> prosa.behavior.time.instant -> bool).
Check (@prosa.model.processor.overheads.is_CRPD :
  forall Job : prosa.behavior.job.JobType,
    OvhSourceScheduleType Job -> prosa.behavior.time.instant -> bool).
Check (@prosa.model.processor.overheads.total_time_in_dispatch :
  forall Job : prosa.behavior.job.JobType,
    OvhSourceScheduleType Job -> prosa.behavior.time.instant ->
    prosa.behavior.time.instant -> nat).
Check (@prosa.model.processor.overheads.total_time_in_context_switch :
  forall Job : prosa.behavior.job.JobType,
    OvhSourceScheduleType Job -> prosa.behavior.time.instant ->
    prosa.behavior.time.instant -> nat).
Check (@prosa.model.processor.overheads.total_time_in_CRPD :
  forall Job : prosa.behavior.job.JobType,
    OvhSourceScheduleType Job -> prosa.behavior.time.instant ->
    prosa.behavior.time.instant -> nat).

Definition OvhTargetScheduleType
    (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job) : Type :=
  ImportedOverheads.Prosa_Behavior_Schedule_schedule_inst4 Job deq
    (ImportedOverheads.Prosa_Model_Processor_Overheads_processor_state Job deq).

Check (ImportedOverheads.Prosa_Model_Processor_Overheads_scheduled_job :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    OvhTargetScheduleType Job deq ->
    ImportedOverheads.Prosa_Behavior_Time_instant -> ImportedOverheads.Option Job).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_is_progress :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    OvhTargetScheduleType Job deq ->
    ImportedOverheads.Prosa_Behavior_Time_instant -> ImportedOverheads.Bool).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_is_context_switch :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    OvhTargetScheduleType Job deq ->
    ImportedOverheads.Prosa_Behavior_Time_instant -> ImportedOverheads.Bool).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_is_dispatch :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    OvhTargetScheduleType Job deq ->
    ImportedOverheads.Prosa_Behavior_Time_instant -> ImportedOverheads.Bool).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_is_CRPD :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    OvhTargetScheduleType Job deq ->
    ImportedOverheads.Prosa_Behavior_Time_instant -> ImportedOverheads.Bool).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_total_time_in_dispatch :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    OvhTargetScheduleType Job deq ->
    ImportedOverheads.Prosa_Behavior_Time_instant ->
    ImportedOverheads.Prosa_Behavior_Time_instant -> Lean.Nat).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_total_time_in_context_switch :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    OvhTargetScheduleType Job deq ->
    ImportedOverheads.Prosa_Behavior_Time_instant ->
    ImportedOverheads.Prosa_Behavior_Time_instant -> Lean.Nat).
Check (ImportedOverheads.Prosa_Model_Processor_Overheads_total_time_in_CRPD :
  forall (Job : ImportedOverheads.Prosa_Behavior_Job_JobType)
    (deq : ImportedOverheads.DecidableEq Job),
    OvhTargetScheduleType Job deq ->
    ImportedOverheads.Prosa_Behavior_Time_instant ->
    ImportedOverheads.Prosa_Behavior_Time_instant -> Lean.Nat).
