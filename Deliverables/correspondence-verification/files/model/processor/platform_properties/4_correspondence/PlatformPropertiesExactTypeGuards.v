From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPlatformPropertiesWithInterface.
From FoundationCertificates Require Import PlatformScheduleBaseAdapter.

(** These guards are separate from the correspondence proof.  They invoke the
    official and imported theorem constants only to make Rocq check that the
    implication used by the certificate is their exact elaborated type. *)

Definition source_unit_supply_is_unit_service_type_guard
    (Job : eqType)
    (PStateR : prosa.behavior.schedule.ProcessorState Job) :
    @prosa.model.processor.platform_properties.unit_supply_proc_model Job
      PStateR ->
    @prosa.model.processor.platform_properties.unit_service_proc_model Job
      PStateR :=
  @prosa.model.processor.platform_properties.unit_supply_is_unit_service
    Job PStateR.

Definition target_unit_supply_is_unit_service_type_guard
    (Job : eqType)
    (PStateL :
      ImportedPlatformPropertiesWithInterface.Prosa_Behavior_Schedule_ProcessorState
        Job (sch_decidable_eq Job)) :
    ImportedPlatformPropertiesWithInterface.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
      Job (sch_decidable_eq Job) PStateL ->
    ImportedPlatformPropertiesWithInterface.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model
      Job (sch_decidable_eq Job) PStateL :=
  ImportedPlatformPropertiesWithInterface.Prosa_Model_Processor_PlatformProperties_unit_supply_is_unit_service
    Job (sch_decidable_eq Job) PStateL.

Check @source_unit_supply_is_unit_service_type_guard.
Check @target_unit_supply_is_unit_service_type_guard.
