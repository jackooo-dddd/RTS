(* Re-bound copy of accepted certificates/analysis/PeriodicCorrespondence.v for the analysis/facts/model/sbf/periodic
   artifact; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From prosa Require Import analysis.definitions.sbf.periodic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSbfPeriodic ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  SupplyBaseAdapter SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations
  SupplyScheduleOperations SupplyNatBoolOperations SupplyIntervalOperations
  SupplyCorrespondence NatSubCorrespondence DivModCorrespondence.

(** All value operations below are replayed and kernel-checked against this
    exact imported Lean module, not identified with another artifact. *)

Lemma prm_sbf_correspondence
    (periodR allocationR deltaR : nat)
    (periodL allocationL deltaL : Lean.Nat) :
  SubNatRel periodR periodL ->
  SubNatRel allocationR allocationL ->
  SubNatRel deltaR deltaL ->
  SubNatRel
    (prosa.analysis.definitions.sbf.periodic.prm_sbf
      periodR allocationR deltaR)
    (ImportedFactsSbfPeriodic.Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf
      periodL allocationL deltaL).
Proof.
  intros Hperiod Halloc Hdelta.
  unfold prosa.analysis.definitions.sbf.periodic.prm_sbf.
  cbn [ImportedFactsSbfPeriodic.Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf].
  pose blackoutR := periodR - allocationR.
  pose blackoutL := dm_imported_sub periodL allocationL.
  have Hblackout : SubNatRel blackoutR blackoutL :=
    dm_sub_correspondence _ _ _ _ Hperiod Halloc.
  pose fullR := (deltaR - blackoutR) %/ periodR.
  pose fullL := dm_imported_div
    (dm_imported_sub deltaL blackoutL) periodL.
  have Hfull : SubNatRel fullR fullL :=
    dm_div_correspondence _ _ _ _
      (dm_sub_correspondence _ _ _ _ Hdelta Hblackout) Hperiod.
  have Htwo : SubNatRel 2
      (ImportedFactsSbfPeriodic.OfNat_ofNat_inst1 Lean.Nat
        (Lean.Nat_succ (Lean.Nat_succ Lean.Nat_zero))
        (ImportedFactsSbfPeriodic.instOfNatNat
          (Lean.Nat_succ (Lean.Nat_succ Lean.Nat_zero)))) :=
    sub_nat_rel_canonical 2.
  change (SubNatRel
    (fullR * allocationR + (deltaR - 2 * blackoutR - fullR * periodR))
    (dm_imported_add (dm_imported_mul fullL allocationL)
      (dm_imported_sub
        (dm_imported_sub deltaL
          (dm_imported_mul
            (ImportedFactsSbfPeriodic.OfNat_ofNat_inst1 Lean.Nat
              (Lean.Nat_succ (Lean.Nat_succ Lean.Nat_zero))
              (ImportedFactsSbfPeriodic.instOfNatNat
                (Lean.Nat_succ (Lean.Nat_succ Lean.Nat_zero))))
            blackoutL))
        (dm_imported_mul fullL periodL)))).
  apply dm_add_correspondence.
  - exact (dm_mul_correspondence _ _ _ _ Hfull Halloc).
  - apply dm_sub_correspondence.
    + apply dm_sub_correspondence; first exact Hdelta.
      exact (dm_mul_correspondence _ _ _ _ Htwo Hblackout).
    + exact (dm_mul_correspondence _ _ _ _ Hfull Hperiod).
Qed.

Section PeriodicResourceModel.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedFactsSbfPeriodic.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).
  Variable Rstate : SupplyProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedFactsSbfPeriodic.Prosa_Behavior_Schedule_schedule Job
    (sch_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SupplyScheduleRel Job PStateR PStateL Rstate schedR schedL.

  Lemma periodic_bound_correspondence
      (periodR allocationR kR : nat)
      (periodL allocationL kL : Lean.Nat) :
    SubNatRel periodR periodL ->
    SubNatRel allocationR allocationL ->
    SubNatRel kR kL ->
    PropSPropRel
      (is_true (leq allocationR
        (@prosa.model.processor.supply.supply_during Job PStateR schedR
          (periodR * kR) (periodR * (kR + 1)))))
      (dm_imported_le allocationL
        (ImportedFactsSbfPeriodic.Prosa_Model_Processor_Supply_supply_during
          Job (sch_decidable_eq Job) PStateL schedL
          (dm_imported_mul periodL kL)
          (dm_imported_mul periodL
            (dm_imported_add kL dm_imported_one)))).
  Proof.
    intros Hperiod Halloc Hk.
    have Hstart := dm_mul_correspondence _ _ _ _ Hperiod Hk.
    have Hk1 := dm_add_correspondence kR kL 1 dm_imported_one
      Hk (sub_nat_rel_canonical 1).
    have Hend := dm_mul_correspondence _ _ _ _ Hperiod Hk1.
    have Hsupply := supply_during_correspondence
      Job PStateR PStateL Rstate schedR schedL Hsched
      (periodR * kR) (periodR * (kR + 1))
      (dm_imported_mul periodL kL)
      (dm_imported_mul periodL (dm_imported_add kL dm_imported_one))
      Hstart Hend.
    exact (dm_le_correspondence _ _ _ _ Halloc Hsupply).
  Qed.

  Lemma periodic_resource_model_correspondence
      (periodR allocationR : nat)
      (periodL allocationL : Lean.Nat) :
    SubNatRel periodR periodL ->
    SubNatRel allocationR allocationL ->
    PropSPropRel
      (@prosa.analysis.definitions.sbf.periodic.periodic_resource_model
        Job PStateR periodR allocationR schedR)
      (ImportedFactsSbfPeriodic.Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model
        Job (sch_decidable_eq Job) PStateL periodL allocationL schedL).
  Proof.
    intros Hperiod Halloc.
    unfold prosa.analysis.definitions.sbf.periodic.periodic_resource_model.
    cbn [ImportedFactsSbfPeriodic.Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model].
    pose Hpositive := dm_lt_correspondence 0 dm_imported_zero
      periodR periodL (sub_nat_rel_canonical 0) Hperiod.
    pose Hcapacity := dm_le_correspondence allocationR allocationL
      periodR periodL Halloc Hperiod.
    apply prop_sprop_rel_intro.
    - intros [Hp [Hc Hb]].
      apply (And_intro _ _
        (prop_to_sprop _ _ Hpositive Hp)).
      apply (And_intro _ _
        (prop_to_sprop _ _ Hcapacity Hc)).
      intros kL.
      pose kR := sub_nat_to_rocq kL.
      have Hk : SubNatRel kR kL := sub_nat_rel_surjective kL.
      exact (prop_to_sprop _ _
        (periodic_bound_correspondence _ _ _ _ _ _
          Hperiod Halloc Hk) (Hb kR)).
    - intro Htarget. apply strictly_inhabits.
      split.
      + exact (sprop_to_prop _ _ Hpositive
          (ImportedFactsSbfPeriodic.And_left _ _ Htarget)).
      + split.
        * exact (sprop_to_prop _ _ Hcapacity
            (ImportedFactsSbfPeriodic.And_left _ _
              (ImportedFactsSbfPeriodic.And_right _ _ Htarget))).
        * intro kR.
          pose kL := sub_nat_to_imported kR.
          have Hk : SubNatRel kR kL := sub_nat_rel_canonical kR.
          exact (sprop_to_prop _ _
            (periodic_bound_correspondence _ _ _ _ _ _
              Hperiod Halloc Hk)
            (ImportedFactsSbfPeriodic.And_right _ _
              (ImportedFactsSbfPeriodic.And_right _ _ Htarget) kL)).
  Qed.

End PeriodicResourceModel.
