From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.definitions.sbf.plain.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPlain.
From FoundationCertificates Require Import SupplyScheduleBaseAdapter.

(** Deliberately separate from the semantic certificate: these guards check
    the official and compiled theorem constants against precisely the two
    statement types structurally related by PlainCorrespondence.v. *)
Section PlainTheoremGuards.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedPlain.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : ImportedPlain.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (sch_decidable_eq Job).
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedPlain.Prosa_Behavior_Schedule_schedule Job
    (sch_decidable_eq Job) PStateL.
  Variable sbfR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction.
  Variable sbfL : ImportedPlain.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction.

  Check (@prosa.analysis.definitions.sbf.plain.sbf_respected_simplified
    Job PStateR arrR schedR sbfR :
      (@prosa.analysis.definitions.sbf.plain.supply_bound_function_respected
        Job PStateR arrR schedR sbfR) ->
      forall (j : Job) (t1R t2R : nat),
        prosa.behavior.arrival_sequence.arrives_in arrR j ->
        is_true (leq t1R t2R) ->
        is_true (leq (sbfR (t2R - t1R))
          (@prosa.model.processor.supply.supply_during
            Job PStateR schedR t1R t2R))).

  Check (ImportedPlain.Prosa_Analysis_Definitions_Sbf_Plain_sbf_respected_simplified
    Job (sch_decidable_eq Job) PStateL arrL schedL sbfL :
      (ImportedPlain.Prosa_Analysis_Definitions_Sbf_Plain_supply_bound_function_respected
        Job (sch_decidable_eq Job) PStateL arrL schedL
        (ImportedPlain.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
          sbfL)) ->
      forall (j : Job) (t1L t2L : Lean.Nat),
        ImportedPlain.Prosa_Behavior_Arrival_sequence_arrives_in
          Job (sch_decidable_eq Job) arrL j ->
        ImportedPlain.LE_le_inst1 Lean.Nat ImportedPlain.instLENat t1L t2L ->
        ImportedPlain.LE_le_inst1 Lean.Nat ImportedPlain.instLENat
          (ImportedPlain.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            sbfL (ImportedPlain.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
              (ImportedPlain.instHSub_inst1 Lean.Nat ImportedPlain.instSubNat)
              t2L t1L))
          (ImportedPlain.Prosa_Model_Processor_Supply_supply_during
            Job (sch_decidable_eq Job) PStateL schedL t1L t2L)).
End PlainTheoremGuards.
