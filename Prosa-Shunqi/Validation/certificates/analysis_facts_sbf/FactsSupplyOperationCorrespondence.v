(* Re-bound copy of accepted certificates/analysis_facts_behavior_supply/FactsSupplyOperationCorrespondence.v for the analysis/facts/SBF artifact;
   only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.facts.behavior.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSbfFacts
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence FsScheduleBaseAdapter
  FsScheduleFiniteOperations FsScheduleCorrespondence
  FsProcessorStateCorrespondence SupplyBaseAdapter
  SupplyNatBoolOperations SupplyIntervalOperations.

(** Compositional operation bridges against the exact imported facts artifact.
    ProcessorState observations use the accepted two-sided Schedule relation;
    interval sums use the accepted Supply list-fold correspondence. *)

Lemma fs_bool_to_nat_related (bR : bool)
    (bL : ImportedSbfFacts.Bool) :
  SvcBoolRel bR bL ->
  SubNatRel (nat_of_bool bR) (ImportedSbfFacts.Bool_toNat bL).
Proof.
  intro Hb. destruct bR, bL; cbn in Hb |- *.
  - exact (svc_false_elim _
      (svc_false_ne_true (sub_imported_eq_sym _ _ Hb))).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical O).
  - exact (svc_false_elim _ (svc_false_ne_true Hb)).
Qed.

Section FactsSupplyOperations.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSbfFacts.Prosa_Behavior_Schedule_ProcessorState
      Job (sch_decidable_eq Job).
  Variable R : SchProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL :
    ImportedSbfFacts.Prosa_Behavior_Schedule_schedule
      Job (sch_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SchScheduleRel Job PStateR PStateL
      (sch_ps_state_rel Job PStateR PStateL R) schedR schedL.

  Lemma fs_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (ImportedSbfFacts.Prosa_Behavior_Service_scheduled_at
        Job (sch_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.scheduled_at.
    cbn [ImportedSbfFacts.Prosa_Behavior_Service_scheduled_at].
    change (SchBoolRel
      (@prosa.behavior.schedule.scheduled_in Job PStateR j (schedR tR))
      (ImportedSbfFacts.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
        Job (sch_decidable_eq Job) PStateL j (schedL tL))).
    exact (scheduled_in_certificate Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma fs_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel
      (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (ImportedSbfFacts.Prosa_Behavior_Service_service_at
        Job (sch_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [ImportedSbfFacts.Prosa_Behavior_Service_service_at].
    exact (service_in_certificate Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma fs_supply_at_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel
      (@prosa.model.processor.supply.supply_at Job PStateR schedR tR)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at
        Job (sch_decidable_eq Job) PStateL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.supply_at.
    cbn [ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at].
    exact (supply_in_certificate Job PStateR PStateL R
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma fs_has_supply_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.model.processor.supply.has_supply Job PStateR schedR tR)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_has_supply
        Job (sch_decidable_eq Job) PStateL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.has_supply.
    cbn [ImportedSbfFacts.Prosa_Model_Processor_Supply_has_supply].
    exact (svc_decide_lt_related O svc_target_zero _ _
      (sub_nat_rel_canonical O) (fs_supply_at_related tR tL Ht)).
  Qed.

  Lemma fs_is_blackout_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.model.processor.supply.is_blackout Job PStateR schedR tR)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout
        Job (sch_decidable_eq Job) PStateL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.is_blackout.
    cbn [ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout].
    exact (svc_bool_not_related _ _ (fs_has_supply_related tR tL Ht)).
  Qed.

  Lemma fs_supply_during_related
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@prosa.model.processor.supply.supply_during Job PStateR
        schedR t1R t2R)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_during
        Job (sch_decidable_eq Job) PStateL schedL t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.model.processor.supply.supply_at Job PStateR
        schedR t)
      (fun t => ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at
        Job (sch_decidable_eq Job) PStateL schedL t)
      Ht1 Ht2 (fun tR tL Ht => fs_supply_at_related tR tL Ht).
    change (SubNatRel
      (@prosa.model.processor.supply.supply_during Job PStateR
        schedR t1R t2R)
      (ImportedSbfFacts.Prosa_Validation_SupplyInterface_supplyDuringProjection
        Job (sch_decidable_eq Job) PStateL schedL t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma fs_blackout_during_related
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@prosa.model.processor.supply.blackout_during Job PStateR
        schedR t1R t2R)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
        Job (sch_decidable_eq Job) PStateL schedL t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => nat_of_bool
        (@prosa.model.processor.supply.is_blackout Job PStateR schedR t))
      (fun t => ImportedSbfFacts.Bool_toNat
        (ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout
          Job (sch_decidable_eq Job) PStateL schedL t))
      Ht1 Ht2
      (fun tR tL Ht => fs_bool_to_nat_related _ _
        (fs_is_blackout_related tR tL Ht)).
    change (SubNatRel
      (@prosa.model.processor.supply.blackout_during Job PStateR
        schedR t1R t2R)
      (ImportedSbfFacts.Prosa_Validation_SupplyInterface_blackoutDuringProjection
        Job (sch_decidable_eq Job) PStateL schedL t1L t2L)) in Hsum.
    exact Hsum.
  Qed.
End FactsSupplyOperations.

Print Assumptions fs_bool_to_nat_related.
Print Assumptions fs_scheduled_at_related.
Print Assumptions fs_service_at_related.
Print Assumptions fs_supply_at_related.
Print Assumptions fs_has_supply_related.
Print Assumptions fs_is_blackout_related.
Print Assumptions fs_supply_during_related.
Print Assumptions fs_blackout_during_related.
