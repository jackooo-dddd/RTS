(* Re-bound copy of accepted .work/experiments/analysis_sbf_pred/certificates/SupplyCorrespondence.v for the analysis/facts/SBF artifact;
   only the imported module name differs. *)
(** Artifact-local replay: the only source rewrite is the imported module identity.
    Accepted producer source SHA-256: 6545384f294d3ca14980a23b67bb7c12ca461a862ca67bc46b29448577cb1125.
    Substitution: ImportedSupply -> ImportedSbfFacts.
    This file must be recompiled and audited by Rocq. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import model.processor.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSbfFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence SupplyBaseAdapter
  SupplyNatBoolOperations SupplyIntervalOperations SupplyScheduleBaseAdapter
  SupplyScheduleFiniteOperations SupplyScheduleOperations.

(** Compositional correspondence for all five definitions in
    [model/processor/supply.v].  The target terms are the actual imported Lean
    declarations whose bodies are bound to the smaller computation interface
    by kernel-checked guards. *)

Lemma supply_bool_to_nat_related (bR : bool) (bL : ImportedSbfFacts.Bool) :
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

Section SupplyCorrespondence.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSbfFacts.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).
  Variable R : SupplyProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedSbfFacts.Prosa_Behavior_Schedule_schedule Job
    (sch_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SupplyScheduleRel Job PStateR PStateL R schedR schedL.

  Lemma supply_at_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.model.processor.supply.supply_at Job PStateR
        schedR tR)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at Job
        (sch_decidable_eq Job) PStateL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.supply_at.
    cbn [ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at].
    exact (supply_ps_supply_in_related Job PStateR PStateL R
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma supply_during_correspondence
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.model.processor.supply.supply_during Job PStateR
        schedR t1R t2R)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_during Job
        (sch_decidable_eq Job) PStateL schedL t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.model.processor.supply.supply_at Job PStateR
        schedR t)
      (fun t => ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at Job
        (sch_decidable_eq Job) PStateL schedL t)
      Ht1 Ht2 (fun tR tL Ht => supply_at_correspondence tR tL Ht).
    change (SubNatRel
      (@prosa.model.processor.supply.supply_during Job PStateR
        schedR t1R t2R)
      (ImportedSbfFacts.Prosa_Validation_SupplyInterface_supplyDuringProjection
        Job (sch_decidable_eq Job) PStateL schedL t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma has_supply_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.model.processor.supply.has_supply Job PStateR
        schedR tR)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_has_supply Job
        (sch_decidable_eq Job) PStateL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.has_supply.
    cbn [ImportedSbfFacts.Prosa_Model_Processor_Supply_has_supply].
    exact (svc_decide_lt_related O svc_target_zero _ _
      (sub_nat_rel_canonical O) (supply_at_correspondence tR tL Ht)).
  Qed.

  Lemma is_blackout_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.model.processor.supply.is_blackout Job PStateR
        schedR tR)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout Job
        (sch_decidable_eq Job) PStateL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.is_blackout.
    cbn [ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout].
    exact (svc_bool_not_related _ _ (has_supply_correspondence tR tL Ht)).
  Qed.

  Lemma blackout_during_correspondence
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.model.processor.supply.blackout_during Job PStateR
        schedR t1R t2R)
      (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during Job
        (sch_decidable_eq Job) PStateL schedL t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => nat_of_bool
        (@prosa.model.processor.supply.is_blackout Job PStateR schedR t))
      (fun t => ImportedSbfFacts.Bool_toNat
        (ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout Job
          (sch_decidable_eq Job) PStateL schedL t))
      Ht1 Ht2
      (fun tR tL Ht => supply_bool_to_nat_related _ _
        (is_blackout_correspondence tR tL Ht)).
    change (SubNatRel
      (@prosa.model.processor.supply.blackout_during Job PStateR
        schedR t1R t2R)
      (ImportedSbfFacts.Prosa_Validation_SupplyInterface_blackoutDuringProjection
        Job (sch_decidable_eq Job) PStateL schedL t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

End SupplyCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN supply_correspondence". exact I. Qed.
Print Assumptions supply_bool_to_nat_related.
Print Assumptions supply_at_correspondence.
Print Assumptions supply_during_correspondence.
Print Assumptions has_supply_correspondence.
Print Assumptions is_blackout_correspondence.
Print Assumptions blackout_during_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END supply_correspondence". exact I. Qed.
