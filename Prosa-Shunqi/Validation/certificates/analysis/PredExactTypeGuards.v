From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.definitions.sbf.pred.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPred.
From FoundationCertificates Require Import SupplyScheduleBaseAdapter.

(** Only this separate guard mentions the source and target theorem proof
    constants. PredCorrespondence.v does not import this file or either proof. *)
Section Guards.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedPred.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : ImportedPred.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (sch_decidable_eq Job).
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedPred.Prosa_Behavior_Schedule_schedule Job
    (sch_decidable_eq Job) PStateL.
  Variable PR : Job -> nat -> nat -> Prop.
  Variable PL : Job -> Lean.Nat -> Lean.Nat -> SProp.
  Variable sbfR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction.
  Variable sbfL : ImportedPred.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction.

  Check (@prosa.analysis.definitions.sbf.pred.sbf_bounded_by_duration
    Job PStateR arrR schedR PR sbfR :
      (@prosa.analysis.definitions.sbf.pred.valid_pred_sbf
        Job PStateR arrR schedR PR sbfR) ->
      prosa.analysis.definitions.sbf.pred.unit_supply_bound_function sbfR ->
      forall dR : nat, is_true (leq (sbfR dR) dR)).

  Check (ImportedPred.Prosa_Analysis_Definitions_Sbf_Pred_sbf_bounded_by_duration
    Job (sch_decidable_eq Job) PStateL arrL schedL PL sbfL :
      (ImportedPred.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf
        Job (sch_decidable_eq Job) PStateL arrL schedL PL
        (ImportedPred.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
          sbfL)) ->
      ImportedPred.Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
        (ImportedPred.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
          sbfL) ->
      forall dL : Lean.Nat,
        ImportedPred.LE_le_inst1 Lean.Nat ImportedPred.instLENat
          (ImportedPred.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            sbfL dL) dL).
End Guards.
