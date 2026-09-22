From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSchedule.
From FoundationCertificates Require Import ScheduleProcessorStateCorrespondence.

(** Exact official declarations elaborated from the byte-identical pinned
    Prosa v0.6 source module. *)
Check @prosa.behavior.schedule.ProcessorState.
Check @prosa.behavior.schedule.Build_ProcessorState.
Check @prosa.behavior.schedule.State.
Check @prosa.behavior.schedule.Core.
Check @prosa.behavior.schedule.scheduled_on.
Check @prosa.behavior.schedule.supply_on.
Check @prosa.behavior.schedule.service_on.
Check @prosa.behavior.schedule.service_on_le_supply_on.
Check @prosa.behavior.schedule.service_on_implies_scheduled_on.
Check @prosa.behavior.schedule.scheduled_in.
Check @prosa.behavior.schedule.supply_in.
Check @prosa.behavior.schedule.service_in.
Check @prosa.behavior.schedule.schedule.

(** Actual declarations imported from the frozen compiled Lean artifact. *)
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_mk.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_Core.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_coreFintype.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_coreDecidableEq.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_on.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_supply_on.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_service_on.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_service_on_le_supply_on.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_service_on_implies_scheduled_on.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_in.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_supply_in.
Check ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_service_in.
Check ImportedSchedule.Prosa_Behavior_Schedule_schedule.

(** The certificate types directly mention the two interfaces above.  Their
    successful elaboration is the exact-type guard for the propositions that
    the assumption audit classifies. *)
Check processor_state_observational_correspondence.
Check scheduled_in_certificate.
Check supply_in_certificate.
Check service_in_certificate.
Check schedule_import_certificate.
Check schedule_export_certificate.
