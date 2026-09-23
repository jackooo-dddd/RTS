From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.definitions.schedule_prefix.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSchedulePrefix.
From FoundationCertificates Require Import ServiceBaseAdapter.

(** These checks bind the independently proved structural relations to the
    two official Rocq theorem types and two exact imported compiled Lean
    theorem types.  The theorem constants are not used in the proofs. *)
Section ExactTypeGuards.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSchedulePrefix.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).

  Check (@prosa.analysis.definitions.schedule_prefix.identical_prefix_scheduled_at
    Job PStateR :
    forall (sched sched' : @prosa.behavior.schedule.schedule Job PStateR)
      (h : nat),
      @prosa.analysis.definitions.schedule_prefix.identical_prefix
        Job PStateR sched sched' h ->
      forall (j : Job) (t : nat), (t < h)%N ->
        Logic.eq
          (@prosa.behavior.service.scheduled_at Job PStateR sched j t)
          (@prosa.behavior.service.scheduled_at Job PStateR sched' j t)).

  Check (ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_scheduled_at
    Job (svc_decidable_eq Job) PStateL :
    forall (sched sched' : ImportedSchedulePrefix.Prosa_Behavior_Schedule_schedule
        Job (svc_decidable_eq Job) PStateL) (h : Lean.Nat),
      ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
        Job (svc_decidable_eq Job) PStateL sched sched' h ->
      forall (j : Job) (t : Lean.Nat),
        ImportedSchedulePrefix.LT_lt_inst1 Lean.Nat
          ImportedSchedulePrefix.instLTNat t h ->
        Lean.eq
          (ImportedSchedulePrefix.Prosa_Behavior_Service_scheduled_at
            Job (svc_decidable_eq Job) PStateL sched j t)
          (ImportedSchedulePrefix.Prosa_Behavior_Service_scheduled_at
            Job (svc_decidable_eq Job) PStateL sched' j t)).

  Check (@prosa.analysis.definitions.schedule_prefix.identical_prefix_inclusion
    Job PStateR :
    forall (sched sched' : @prosa.behavior.schedule.schedule Job PStateR)
      (h h' : nat),
      (h' <= h)%N ->
      @prosa.analysis.definitions.schedule_prefix.identical_prefix
        Job PStateR sched sched' h ->
      @prosa.analysis.definitions.schedule_prefix.identical_prefix
        Job PStateR sched sched' h').

  Check (ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_inclusion
    Job (svc_decidable_eq Job) PStateL :
    forall (sched sched' : ImportedSchedulePrefix.Prosa_Behavior_Schedule_schedule
        Job (svc_decidable_eq Job) PStateL) (h h' : Lean.Nat),
      ImportedSchedulePrefix.LE_le_inst1 Lean.Nat
        ImportedSchedulePrefix.instLENat h' h ->
      ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
        Job (svc_decidable_eq Job) PStateL sched sched' h ->
      ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
        Job (svc_decidable_eq Job) PStateL sched sched' h').
End ExactTypeGuards.
