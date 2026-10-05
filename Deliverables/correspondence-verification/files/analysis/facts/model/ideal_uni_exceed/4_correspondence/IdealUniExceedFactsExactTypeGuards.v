From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.facts.model.ideal_uni_exceed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealUniExceedFacts.
From FoundationCertificates Require Import IdealUniExceedFactsBaseAdapter.

(** All seven guards elaborate the official source constant and the imported
    production Lean constant against an explicit expected type. *)
Section ExactTypeGuards.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let stateL :=
    ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state
      Job (iue_decidable_eq Job).

  Definition source_eps_is_unit_supply_guard :
      @prosa.model.processor.platform_properties.unit_supply_proc_model
        Job stateR :=
    @prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_supply Job.
  Definition target_eps_is_unit_supply_guard :
      ImportedIdealUniExceedFacts.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4
        Job (iue_decidable_eq Job) stateL :=
    ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_eps_is_unit_supply
      Job (iue_decidable_eq Job).

  Definition source_eps_is_uniproc_guard :
      @prosa.model.processor.platform_properties.uniprocessor_model
        Job stateR :=
    @prosa.analysis.facts.model.ideal_uni_exceed.eps_is_uniproc Job.
  Definition target_eps_is_uniproc_guard :
      ImportedIdealUniExceedFacts.Prosa_Model_Processor_PlatformProperties_uniprocessor_model_inst4
        Job (iue_decidable_eq Job) stateL :=
    ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_eps_is_uniproc
      Job (iue_decidable_eq Job).

  Definition source_eps_is_fully_consuming_guard :
      @prosa.model.processor.platform_properties.fully_consuming_proc_model
        Job stateR :=
    @prosa.analysis.facts.model.ideal_uni_exceed.eps_is_fully_consuming Job.
  Definition target_eps_is_fully_consuming_guard :
      ImportedIdealUniExceedFacts.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4
        Job (iue_decidable_eq Job) stateL :=
    ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_eps_is_fully_consuming
      Job (iue_decidable_eq Job).

  Definition source_eps_is_unit_service_guard :
      @prosa.model.processor.platform_properties.unit_service_proc_model
        Job stateR :=
    @prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_service Job.
  Definition target_eps_is_unit_service_guard :
      ImportedIdealUniExceedFacts.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model_inst4
        Job (iue_decidable_eq Job) stateL :=
    ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_eps_is_unit_service
      Job (iue_decidable_eq Job).

  Definition source_is_exceedance_exec_guard :
      @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job -> bool :=
    @prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec Job.
  Definition target_is_exceedance_exec_guard :
      ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job ->
      ImportedIdealUniExceedFacts.Bool :=
    ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec
      Job (iue_decidable_eq Job).

  Definition source_scheduled_at_procstate_guard
      (sched : @prosa.behavior.schedule.schedule Job stateR)
      (j : Job) (t : prosa.behavior.time.instant) :
      @prosa.behavior.service.scheduled_at Job stateR sched j t <->
        sched t = @prosa.model.processor.ideal_uni_exceed.NominalExecution Job j \/
        sched t = @prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job j :=
    @prosa.analysis.facts.model.ideal_uni_exceed.scheduled_at_procstate
      Job sched j t.
  Definition target_scheduled_at_procstate_guard
      (sched : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL)
      (j : Job) (t : Lean.Nat) :
      ImportedIdealUniExceedFacts.Iff
        (Lean.eq
          (ImportedIdealUniExceedFacts.Prosa_Behavior_Service_scheduled_at_inst4
            Job (iue_decidable_eq Job) stateL sched j t)
          ImportedIdealUniExceedFacts.Bool_true)
        (Lean.Or
          (Lean.eq (sched t)
            (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution
              Job j))
          (Lean.eq (sched t)
            (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution
              Job j))) :=
    ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_scheduled_at_procstate
      Job (iue_decidable_eq Job) sched j t.

  Definition source_blackout_guard
      (sched : @prosa.behavior.schedule.schedule Job stateR)
      (t : prosa.behavior.time.instant) :
      @prosa.model.processor.supply.is_blackout Job stateR sched t =
        @prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec
          Job (sched t) :=
    @prosa.analysis.facts.model.ideal_uni_exceed.blackout_implies_exceedance_execution
      Job sched t.
  Definition target_blackout_guard
      (sched : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL)
      (t : Lean.Nat) :
      Lean.eq
        (ImportedIdealUniExceedFacts.Prosa_Model_Processor_Supply_is_blackout_inst4
          Job (iue_decidable_eq Job) stateL sched t)
        (ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec
          Job (iue_decidable_eq Job) (sched t)) :=
    ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_blackout_implies_exceedance_execution
      Job (iue_decidable_eq Job) sched t.
End ExactTypeGuards.
