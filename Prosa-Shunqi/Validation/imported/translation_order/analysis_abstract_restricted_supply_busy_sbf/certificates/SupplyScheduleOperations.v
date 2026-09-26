(* Re-bound copy of accepted .work/experiments/analysis_sbf_pred/certificates/SupplyScheduleOperations.v for the busy_sbf artifact; only the imported module name differs. *)
(** Artifact-local replay: the only source rewrite is the imported module identity.
    Accepted producer source SHA-256: 49c815591a0e385fa8e045b9e779f7f448d0b547011cde4f6595bf3aaee7e519.
    Substitution: ImportedSupply -> ImportedBusySbf.
    This file must be recompiled and audited by Rocq. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusySbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence SupplyScheduleBaseAdapter
  SupplyScheduleFiniteOperations.

(** Supply-only observational relation for the actual imported artifact.
    It intentionally exposes only the ProcessorState observations used by
    [model/processor/supply.v], rather than strengthening the input relation
    with unrelated scheduled/service fields. *)

Section ProcessorStateSupplyObservations.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let CoreR : finType := @prosa.behavior.schedule.Core Job PStateR.
  Let StateL : Type :=
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_State Job
      (sch_decidable_eq Job) PStateL.
  Let CoreL : Type :=
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_Core Job
      (sch_decidable_eq Job) PStateL.

  Definition supply_target_supply_on (s : StateL) (c : CoreL) : Lean.Nat :=
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_supply_on
      Job (sch_decidable_eq Job) PStateL s c.

  Record SupplyProcessorStateRel : Type := {
    supply_ps_state_rel : StateR -> StateL -> SProp;
    supply_ps_core_to_target : CoreR -> CoreL;
    supply_ps_core_enumeration_rel :
      SchCoreEnumerationRel CoreR CoreL supply_ps_core_to_target
        (ImportedBusySbf.Prosa_Validation_ScheduleInterface_coreEnumeration
          Job (sch_decidable_eq Job) PStateL);
    supply_ps_supply_on_rel :
      forall (sR : StateR) (sL : StateL) (cR : CoreR),
        supply_ps_state_rel sR sL ->
        SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
          (supply_target_supply_on sL (supply_ps_core_to_target cR))
  }.

  Variable R : SupplyProcessorStateRel.

  Lemma supply_ps_supply_in_related (sR : StateR) (sL : StateL) :
    supply_ps_state_rel R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_in Job PStateR sR)
      (ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_supply_in
        Job (sch_decidable_eq Job) PStateL sL).
  Proof.
    intro Hstate.
    have Hsum := sch_finite_sum_related CoreR CoreL
      (supply_ps_core_to_target R)
      (fun cR => @prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (supply_target_supply_on sL)
      (ImportedBusySbf.Prosa_Validation_ScheduleInterface_coreEnumeration
        Job (sch_decidable_eq Job) PStateL)
      (fun cR => supply_ps_supply_on_rel R sR sL cR Hstate)
      (supply_ps_core_enumeration_rel R).
    unfold SubNatRel in Hsum |- *.
    exact (sub_imported_eq_trans _ _ _ Hsum
      (sub_imported_eq_sym _ _
        (ImportedBusySbf.Prosa_Validation_ScheduleInterface_production_supply_in_as_list_sum
          Job (sch_decidable_eq Job) PStateL sL))).
  Qed.

  Definition SupplyScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedBusySbf.Prosa_Behavior_Schedule_schedule Job
        (sch_decidable_eq Job) PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      supply_ps_state_rel R (schedR tR) (schedL tL).

End ProcessorStateSupplyObservations.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN supply_schedule_operations". exact I. Qed.
Print Assumptions supply_ps_supply_in_related.
Goal Logic.True.
Proof. idtac "AUDIT_END supply_schedule_operations". exact I. Qed.
