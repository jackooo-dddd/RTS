(* Re-bound copy of accepted certificates/analysis/PlainCorrespondence.v for the analysis/facts/model/sbf/average
   artifact; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.definitions.sbf.plain.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSbfAverage ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence
  SupplyBaseAdapter SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations
  SupplyScheduleOperations SupplyNatBoolOperations SupplyIntervalOperations
  SupplyCorrespondence PredCorrespondence.

(** The always-true predicate is a proved instance of the accepted predicate
    relation; it is not a declaration-specific semantic assumption. *)
Lemma plain_true_predicate_relation (Job : eqType) :
  PredPredicateRel Job
    (fun (_ : Job) (_ _ : nat) => Logic.True)
    (fun (_ : Job) (_ _ : Lean.Nat) => ImportedFactsSbfAverage.True).
Proof.
  intros j t1R t1L t2R t2L Ht1 Ht2.
  apply prop_sprop_rel_intro.
  - intro Htrue. exact ImportedFactsSbfAverage.True_intro.
  - intro Htrue. apply strictly_inhabits. exact Logic.I.
Qed.

Section PlainSupplyBoundFunctions.
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
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : ImportedFactsSbfAverage.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable fR : nat -> nat.
  Variable fL : Lean.Nat -> Lean.Nat.
  Hypothesis Hf : PredFunctionRel fR fL.

  Lemma plain_supply_bound_function_respected_correspondence :
    PropSPropRel
      (@prosa.analysis.definitions.sbf.plain.supply_bound_function_respected
        Job PStateR arrR schedR fR)
      (ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Plain_supply_bound_function_respected
        Job (sch_decidable_eq Job) PStateL arrL schedL fL).
  Proof.
    unfold prosa.analysis.definitions.sbf.plain.supply_bound_function_respected.
    cbn [ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Plain_supply_bound_function_respected].
    exact (pred_sbf_respected_correspondence
      Job PStateR PStateL Rstate schedR schedL Hsched
      arrR arrL Harr _ _ (plain_true_predicate_relation Job)
      fR fL Hf).
  Qed.

  Lemma plain_valid_supply_bound_function_correspondence :
    PropSPropRel
      (@prosa.analysis.definitions.sbf.plain.valid_supply_bound_function
        Job PStateR arrR schedR fR)
      (ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Plain_valid_supply_bound_function
        Job (sch_decidable_eq Job) PStateL arrL schedL fL).
  Proof.
    unfold prosa.analysis.definitions.sbf.plain.valid_supply_bound_function.
    cbn [ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Plain_valid_supply_bound_function].
    exact (pred_valid_pred_sbf_correspondence
      Job PStateR PStateL Rstate schedR schedL Hsched
      arrR arrL Harr _ _ (plain_true_predicate_relation Job)
      fR fL Hf).
  Qed.
End PlainSupplyBoundFunctions.

Section PlainTheoremStatement.
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
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : ImportedFactsSbfAverage.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable sbfR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction.
  Variable sbfL : ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction.
  Hypothesis Hsbf : PredSbfClassRel sbfR sbfL.

  Lemma plain_sbf_respected_simplified_statement_correspondence :
    PropSPropRel
      ((@prosa.analysis.definitions.sbf.plain.supply_bound_function_respected
          Job PStateR arrR schedR sbfR) ->
       forall (j : Job) (t1R t2R : nat),
         prosa.behavior.arrival_sequence.arrives_in arrR j ->
         is_true (leq t1R t2R) ->
         is_true (leq (sbfR (t2R - t1R))
           (@prosa.model.processor.supply.supply_during
             Job PStateR schedR t1R t2R)))
      ((ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_Plain_supply_bound_function_respected
          Job (sch_decidable_eq Job) PStateL arrL schedL
          (ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            sbfL)) ->
       forall (j : Job) (t1L t2L : Lean.Nat),
         ImportedFactsSbfAverage.Prosa_Behavior_Arrival_sequence_arrives_in
           Job (sch_decidable_eq Job) arrL j ->
         ImportedFactsSbfAverage.LE_le_inst1 Lean.Nat ImportedFactsSbfAverage.instLENat t1L t2L ->
         ImportedFactsSbfAverage.LE_le_inst1 Lean.Nat ImportedFactsSbfAverage.instLENat
           (ImportedFactsSbfAverage.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
             sbfL (svc_target_sub t2L t1L))
           (ImportedFactsSbfAverage.Prosa_Model_Processor_Supply_supply_during
             Job (sch_decidable_eq Job) PStateL schedL t1L t2L)).
  Proof.
    apply ar_imp_correspondence.
    - exact (plain_supply_bound_function_respected_correspondence
        Job PStateR PStateL Rstate schedR schedL Hsched arrR arrL Harr
        sbfR _ Hsbf).
    - apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_imp_correspondence.
      + exact (arrives_in_correspondence_certificate
          Job arrR arrL j Harr).
      + apply ar_imp_correspondence.
        * exact (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2).
        * have Hdelta := svc_target_sub_related t2R t2L t1R t1L Ht2 Ht1.
          have Hvalue := Hsbf _ _ Hdelta.
          have Hsupply := supply_during_correspondence
            Job PStateR PStateL Rstate schedR schedL Hsched
            t1R t2R t1L t2L Ht1 Ht2.
          exact (sub_nat_le_correspondence _ _ _ _ Hvalue Hsupply).
  Qed.
End PlainTheoremStatement.

Print Assumptions plain_true_predicate_relation.
Print Assumptions plain_supply_bound_function_respected_correspondence.
Print Assumptions plain_valid_supply_bound_function_correspondence.
Print Assumptions plain_sbf_respected_simplified_statement_correspondence.
