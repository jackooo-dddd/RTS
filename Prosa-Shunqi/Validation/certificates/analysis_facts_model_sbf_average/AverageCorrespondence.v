(* Re-bound copy of accepted certificates/analysis/AverageCorrespondence.v for the analysis/facts/model/sbf/average
   artifact; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From prosa Require Import analysis.definitions.sbf.average.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSbfAverage ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  SupplyBaseAdapter SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations
  SupplyScheduleOperations SupplyNatBoolOperations SupplyIntervalOperations
  SupplyCorrespondence NatSubCorrespondence DivModCorrespondence.

(** The two v0.6 definitions are checked against their compiled Lean bodies.
    All arithmetic uses the replayed accepted DivMod relation on this exact
    imported artifact; no division-equality premise is introduced. *)

Lemma arm_sbf_correspondence
    (periodR allocationR delayR deltaR : nat)
    (periodL allocationL delayL deltaL : Lean.Nat) :
  SubNatRel periodR periodL ->
  SubNatRel allocationR allocationL ->
  SubNatRel delayR delayL ->
  SubNatRel deltaR deltaL ->
  SubNatRel
    (prosa.analysis.definitions.sbf.average.arm_sbf
      periodR allocationR delayR deltaR)
    (ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Average_arm_sbf
      periodL allocationL delayL deltaL).
Proof.
  intros Hperiod Halloc Hdelay Hdelta.
  unfold prosa.analysis.definitions.sbf.average.arm_sbf.
  cbn [ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Average_arm_sbf].
  apply dm_div_correspondence; last exact Hperiod.
  apply dm_mul_correspondence; last exact Halloc.
  exact (dm_sub_correspondence _ _ _ _ Hdelta Hdelay).
Qed.

Lemma average_bound_correspondence
    (periodR allocationR delayR t1R t2R : nat)
    (periodL allocationL delayL t1L t2L : Lean.Nat) :
  SubNatRel periodR periodL ->
  SubNatRel allocationR allocationL ->
  SubNatRel delayR delayL ->
  SubNatRel t1R t1L ->
  SubNatRel t2R t2L ->
  SubNatRel (((t2R - t1R - delayR) * allocationR) %/ periodR)
    (dm_imported_div
      (dm_imported_mul
        (dm_imported_sub (dm_imported_sub t2L t1L) delayL)
        allocationL) periodL).
Proof.
  intros Hperiod Halloc Hdelay Ht1 Ht2.
  apply dm_div_correspondence; last exact Hperiod.
  apply dm_mul_correspondence; last exact Halloc.
  apply dm_sub_correspondence; last exact Hdelay.
  exact (dm_sub_correspondence _ _ _ _ Ht2 Ht1).
Qed.

Section AverageResourceModel.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedFactsSbfAverage.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).
  Variable Rstate : SupplyProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedFactsSbfAverage.Prosa_Behavior_Schedule_schedule Job
    (sch_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SupplyScheduleRel Job PStateR PStateL Rstate schedR schedL.

  Lemma average_resource_model_correspondence
      (periodR allocationR delayR : nat)
      (periodL allocationL delayL : Lean.Nat) :
    SubNatRel periodR periodL ->
    SubNatRel allocationR allocationL ->
    SubNatRel delayR delayL ->
    PropSPropRel
      (@prosa.analysis.definitions.sbf.average.average_resource_model
        Job PStateR periodR allocationR delayR schedR)
      (ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Average_average_resource_model
        Job (sch_decidable_eq Job) PStateL
        periodL allocationL delayL schedL).
  Proof.
    intros Hperiod Halloc Hdelay.
    unfold prosa.analysis.definitions.sbf.average.average_resource_model.
    cbn [ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Average_average_resource_model].
    pose Hunit := dm_le_correspondence allocationR allocationL
      periodR periodL Halloc Hperiod.
    apply prop_sprop_rel_intro.
    - intros [Hu Hb].
      apply (Lean.And_intro _ _ (prop_to_sprop _ _ Hunit Hu)).
      intros t1L t2L.
      pose t1R := sub_nat_to_rocq t1L.
      pose t2R := sub_nat_to_rocq t2L.
      have Ht1 : SubNatRel t1R t1L := sub_nat_rel_surjective t1L.
      have Ht2 : SubNatRel t2R t2L := sub_nat_rel_surjective t2L.
      have Hbound := average_bound_correspondence
        periodR allocationR delayR t1R t2R
        periodL allocationL delayL t1L t2L
        Hperiod Halloc Hdelay Ht1 Ht2.
      have Hsupply := supply_during_correspondence
        Job PStateR PStateL Rstate schedR schedL Hsched
        t1R t2R t1L t2L Ht1 Ht2.
      exact (prop_to_sprop _ _
        (dm_le_correspondence _ _ _ _ Hbound Hsupply)
        (Hb t1R t2R)).
    - intro Htarget. apply strictly_inhabits.
      split.
      + exact (sprop_to_prop _ _ Hunit
          (ImportedFactsSbfAverage.And_left _ _ Htarget)).
      + intros t1R t2R.
        pose t1L := sub_nat_to_imported t1R.
        pose t2L := sub_nat_to_imported t2R.
        have Ht1 : SubNatRel t1R t1L := sub_nat_rel_canonical t1R.
        have Ht2 : SubNatRel t2R t2L := sub_nat_rel_canonical t2R.
        have Hbound := average_bound_correspondence
          periodR allocationR delayR t1R t2R
          periodL allocationL delayL t1L t2L
          Hperiod Halloc Hdelay Ht1 Ht2.
        have Hsupply := supply_during_correspondence
          Job PStateR PStateL Rstate schedR schedL Hsched
          t1R t2R t1L t2L Ht1 Ht2.
        exact (sprop_to_prop _ _
          (dm_le_correspondence _ _ _ _ Hbound Hsupply)
          (ImportedFactsSbfAverage.And_right _ _ Htarget t1L t2L)).
  Qed.

End AverageResourceModel.
