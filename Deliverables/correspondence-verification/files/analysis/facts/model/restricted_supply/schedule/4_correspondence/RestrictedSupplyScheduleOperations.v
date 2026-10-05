From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.facts.model.restricted_supply.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRestrictedSupplySchedule ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  RestrictedSupplyScheduleBaseAdapter RestrictedSupplyScheduleStateCorrespondence
  RestrictedSupplyScheduleSourceComputation.

(** Operation correspondence for the actual compiled finite Unit core folds.
    The right-hand equalities are exported proof bodies from the production
    Lean module, not redefined replacement functions. *)
Section RestrictedSupplyScheduleOperations.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.restricted_supply.rs_processor_state Job.
  Let stateL :=
    ImportedRestrictedSupplySchedule.Prosa_Model_Processor_RestrictedSupply_rs_processor_state
      Job (rs_decidable_eq Job).

  Lemma facts_scheduled_in_correspondence (j : Job)
      (sR : RsSource Job) (sL : RsTarget Job) :
    RsStateRel Job sR sL ->
    RsBoolRel
      (@prosa.behavior.schedule.scheduled_in Job stateR j sR)
      (ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4
        Job (rs_decidable_eq Job) stateL j sL).
  Proof.
    intro Hstate. destruct Hstate.
    rewrite (rss_source_scheduled_in_concrete Job j sR).
    exact (sub_imported_eq_trans _ _ _
      (rs_scheduled_on_correspondence Job j sR)
      (sub_imported_eq_sym _ _
        (ImportedRestrictedSupplySchedule.Prosa_Validation_RestrictedSupplyScheduleInterface_production_scheduled_in_concrete
          Job (rs_decidable_eq Job) j (rs_to_target Job sR)))).
  Qed.

  Lemma facts_supply_in_correspondence
      (sR : RsSource Job) (sL : RsTarget Job) :
    RsStateRel Job sR sL ->
    SubNatRel
      (@prosa.behavior.schedule.supply_in Job stateR sR)
      (ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4
        Job (rs_decidable_eq Job) stateL sL).
  Proof.
    intro Hstate. destruct Hstate.
    rewrite (rss_source_supply_in_concrete Job sR).
    exact (sub_imported_eq_trans _ _ _
      (rs_supply_on_correspondence Job sR)
      (sub_imported_eq_sym _ _
        (ImportedRestrictedSupplySchedule.Prosa_Validation_RestrictedSupplyScheduleInterface_production_supply_in_concrete
          Job (rs_decidable_eq Job) (rs_to_target Job sR)))).
  Qed.

  Lemma facts_service_in_correspondence (j : Job)
      (sR : RsSource Job) (sL : RsTarget Job) :
    RsStateRel Job sR sL ->
    SubNatRel
      (@prosa.behavior.schedule.service_in Job stateR j sR)
      (ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4
        Job (rs_decidable_eq Job) stateL j sL).
  Proof.
    intro Hstate. destruct Hstate.
    rewrite (rss_source_service_in_concrete Job j sR).
    exact (sub_imported_eq_trans _ _ _
      (rs_service_on_correspondence Job j sR)
      (sub_imported_eq_sym _ _
        (ImportedRestrictedSupplySchedule.Prosa_Validation_RestrictedSupplyScheduleInterface_production_service_in_concrete
          Job (rs_decidable_eq Job) j (rs_to_target Job sR)))).
  Qed.

  Definition FactsScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_schedule_inst4
        Job (rs_decidable_eq Job) stateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      RsStateRel Job (schedR tR) (schedL tL).

  Definition facts_schedule_to_target
      (schedR : @prosa.behavior.schedule.schedule Job stateR) :
      ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_schedule_inst4
        Job (rs_decidable_eq Job) stateL :=
    fun tL => rs_to_target Job (schedR (sub_nat_to_rocq tL)).

  Definition facts_schedule_to_source
      (schedL : ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_schedule_inst4
        Job (rs_decidable_eq Job) stateL) :
      @prosa.behavior.schedule.schedule Job stateR :=
    fun tR => rs_to_source Job (schedL (sub_nat_to_imported tR)).

  Lemma facts_schedule_import
      (schedR : @prosa.behavior.schedule.schedule Job stateR) :
    FactsScheduleRel schedR (facts_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. destruct Ht.
    unfold facts_schedule_to_target.
    rewrite (sub_nat_rocq_roundtrip tR).
    exact (@Lean.eq_refl _ _).
  Qed.

  Lemma facts_schedule_export
      (schedL : ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_schedule_inst4
        Job (rs_decidable_eq Job) stateL) :
    FactsScheduleRel (facts_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. destruct Ht.
    unfold facts_schedule_to_source.
    exact (rs_target_roundtrip Job (schedL (sub_nat_to_imported tR))).
  Qed.

  Lemma facts_scheduled_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_schedule_inst4
        Job (rs_decidable_eq Job) stateL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel schedR schedL -> SubNatRel tR tL ->
    RsBoolRel
      (@prosa.behavior.service.scheduled_at Job stateR schedR j tR)
      (ImportedRestrictedSupplySchedule.Prosa_Behavior_Service_scheduled_at_inst4
        Job (rs_decidable_eq Job) stateL schedL j tL).
  Proof.
    intros Hsched Ht.
    change (RsBoolRel
      (@prosa.behavior.schedule.scheduled_in Job stateR j (schedR tR))
      (ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4
        Job (rs_decidable_eq Job) stateL j (schedL tL))).
    exact (facts_scheduled_in_correspondence j _ _ (Hsched tR tL Ht)).
  Qed.

  Lemma facts_service_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_schedule_inst4
        Job (rs_decidable_eq Job) stateL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel schedR schedL -> SubNatRel tR tL ->
    SubNatRel
      (@prosa.behavior.service.service_at Job stateR schedR j tR)
      (ImportedRestrictedSupplySchedule.Prosa_Behavior_Service_service_at_inst4
        Job (rs_decidable_eq Job) stateL schedL j tL).
  Proof.
    intros Hsched Ht.
    change (SubNatRel
      (@prosa.behavior.schedule.service_in Job stateR j (schedR tR))
      (ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4
        Job (rs_decidable_eq Job) stateL j (schedL tL))).
    exact (facts_service_in_correspondence j _ _ (Hsched tR tL Ht)).
  Qed.

  Lemma facts_supply_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_schedule_inst4
        Job (rs_decidable_eq Job) stateL)
      (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel schedR schedL -> SubNatRel tR tL ->
    SubNatRel
      (@prosa.model.processor.supply.supply_at Job stateR schedR tR)
      (ImportedRestrictedSupplySchedule.Prosa_Model_Processor_Supply_supply_at_inst4
        Job (rs_decidable_eq Job) stateL schedL tL).
  Proof.
    intros Hsched Ht.
    change (SubNatRel
      (@prosa.behavior.schedule.supply_in Job stateR (schedR tR))
      (ImportedRestrictedSupplySchedule.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4
        Job (rs_decidable_eq Job) stateL (schedL tL))).
    exact (facts_supply_in_correspondence _ _ (Hsched tR tL Ht)).
  Qed.
End RestrictedSupplyScheduleOperations.

Print Assumptions facts_scheduled_in_correspondence.
Print Assumptions facts_supply_in_correspondence.
Print Assumptions facts_service_in_correspondence.
Print Assumptions facts_schedule_import.
Print Assumptions facts_schedule_export.
Print Assumptions facts_scheduled_at_correspondence.
Print Assumptions facts_service_at_correspondence.
Print Assumptions facts_supply_at_correspondence.
