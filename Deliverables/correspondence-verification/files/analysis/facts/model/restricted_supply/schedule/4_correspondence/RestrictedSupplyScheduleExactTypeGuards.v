From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.facts.model.restricted_supply.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRestrictedSupplySchedule.
From FoundationCertificates Require Import RestrictedSupplyScheduleBaseAdapter.

(** All three source constants and all three imported production constants
    elaborate at their exact predicate types, without proxy statements. *)
Section ExactTypeGuards.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.restricted_supply.rs_processor_state Job.
  Let stateL :=
    ImportedRestrictedSupplySchedule.Prosa_Model_Processor_RestrictedSupply_rs_processor_state
      Job (rs_decidable_eq Job).

  Definition source_uniprocessor_guard :
      @prosa.model.processor.platform_properties.uniprocessor_model
        Job stateR :=
    @prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_is_a_uniprocessor_model
      Job.
  Definition target_uniprocessor_guard :
      ImportedRestrictedSupplySchedule.Prosa_Model_Processor_PlatformProperties_uniprocessor_model_inst4
        Job (rs_decidable_eq Job) stateL :=
    ImportedRestrictedSupplySchedule.Prosa_Analysis_Facts_Model_RestrictedSupply_Schedule_rs_proc_model_is_a_uniprocessor_model
      Job (rs_decidable_eq Job).

  Definition source_unit_supply_guard :
      @prosa.model.processor.platform_properties.unit_supply_proc_model
        Job stateR :=
    @prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_is_unit_supply
      Job.
  Definition target_unit_supply_guard :
      ImportedRestrictedSupplySchedule.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4
        Job (rs_decidable_eq Job) stateL :=
    ImportedRestrictedSupplySchedule.Prosa_Analysis_Facts_Model_RestrictedSupply_Schedule_rs_proc_is_unit_supply
      Job (rs_decidable_eq Job).

  Definition source_fully_consuming_guard :
      @prosa.model.processor.platform_properties.fully_consuming_proc_model
        Job stateR :=
    @prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_fully_consuming
      Job.
  Definition target_fully_consuming_guard :
      ImportedRestrictedSupplySchedule.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4
        Job (rs_decidable_eq Job) stateL :=
    ImportedRestrictedSupplySchedule.Prosa_Analysis_Facts_Model_RestrictedSupply_Schedule_rs_proc_model_fully_consuming
      Job (rs_decidable_eq Job).
End ExactTypeGuards.

Print Assumptions source_uniprocessor_guard.
Print Assumptions target_uniprocessor_guard.
Print Assumptions source_unit_supply_guard.
Print Assumptions target_unit_supply_guard.
Print Assumptions source_fully_consuming_guard.
Print Assumptions target_fully_consuming_guard.
