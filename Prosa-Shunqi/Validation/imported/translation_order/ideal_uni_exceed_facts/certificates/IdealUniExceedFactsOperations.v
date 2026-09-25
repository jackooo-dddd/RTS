From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.facts.model.ideal_uni_exceed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealUniExceedFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  IdealUniExceedFactsBaseAdapter IdealUniExceedFactsStateCorrespondence
  IdealUniExceedFactsSourceComputation.

(** Operation correspondence for the actual compiled finite Unit core folds.
    The right-hand equalities are exported proof bodies from the production
    Lean module, not redefined replacement functions. *)
Section IdealUniExceedFactsOperations.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let stateL :=
    ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state
      Job (iue_decidable_eq Job).

  Lemma facts_scheduled_in_correspondence (j : Job)
      (sR : IueSource Job) (sL : IueTarget Job) :
    IueRel Job sR sL ->
    IueBoolRel
      (@prosa.behavior.schedule.scheduled_in Job stateR j sR)
      (ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4
        Job (iue_decidable_eq Job) stateL j sL).
  Proof.
    intro Hstate. destruct Hstate.
    rewrite (facts_source_scheduled_in_concrete Job j sR).
    exact (sub_imported_eq_trans _ _ _
      (iue_scheduled_on_correspondence Job j sR)
      (sub_imported_eq_sym _ _
        (ImportedIdealUniExceedFacts.Prosa_Validation_IdealUniExceedFactsInterface_production_scheduled_in_concrete
          Job (iue_decidable_eq Job) j (iue_to_target Job sR)))).
  Qed.

  Lemma facts_supply_in_correspondence
      (sR : IueSource Job) (sL : IueTarget Job) :
    IueRel Job sR sL ->
    SubNatRel
      (@prosa.behavior.schedule.supply_in Job stateR sR)
      (ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4
        Job (iue_decidable_eq Job) stateL sL).
  Proof.
    intro Hstate. destruct Hstate.
    rewrite (facts_source_supply_in_concrete Job sR).
    exact (sub_imported_eq_trans _ _ _
      (iue_supply_on_correspondence Job sR)
      (sub_imported_eq_sym _ _
        (ImportedIdealUniExceedFacts.Prosa_Validation_IdealUniExceedFactsInterface_production_supply_in_concrete
          Job (iue_decidable_eq Job) (iue_to_target Job sR)))).
  Qed.

  Lemma facts_service_in_correspondence (j : Job)
      (sR : IueSource Job) (sL : IueTarget Job) :
    IueRel Job sR sL ->
    SubNatRel
      (@prosa.behavior.schedule.service_in Job stateR j sR)
      (ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4
        Job (iue_decidable_eq Job) stateL j sL).
  Proof.
    intro Hstate. destruct Hstate.
    rewrite (facts_source_service_in_concrete Job j sR).
    exact (sub_imported_eq_trans _ _ _
      (iue_service_on_correspondence Job j sR)
      (sub_imported_eq_sym _ _
        (ImportedIdealUniExceedFacts.Prosa_Validation_IdealUniExceedFactsInterface_production_service_in_concrete
          Job (iue_decidable_eq Job) j (iue_to_target Job sR)))).
  Qed.

  Definition FactsScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      IueRel Job (schedR tR) (schedL tL).

  Definition facts_schedule_to_target
      (schedR : @prosa.behavior.schedule.schedule Job stateR) :
      ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL :=
    fun tL => iue_to_target Job (schedR (sub_nat_to_rocq tL)).

  Definition facts_schedule_to_source
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL) :
      @prosa.behavior.schedule.schedule Job stateR :=
    fun tR => iue_to_source Job (schedL (sub_nat_to_imported tR)).

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
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL) :
    FactsScheduleRel (facts_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. destruct Ht.
    unfold facts_schedule_to_source.
    exact (iue_target_roundtrip Job (schedL (sub_nat_to_imported tR))).
  Qed.

  Lemma facts_scheduled_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel schedR schedL -> SubNatRel tR tL ->
    IueBoolRel
      (@prosa.behavior.service.scheduled_at Job stateR schedR j tR)
      (ImportedIdealUniExceedFacts.Prosa_Behavior_Service_scheduled_at_inst4
        Job (iue_decidable_eq Job) stateL schedL j tL).
  Proof.
    intros Hsched Ht.
    change (IueBoolRel
      (@prosa.behavior.schedule.scheduled_in Job stateR j (schedR tR))
      (ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4
        Job (iue_decidable_eq Job) stateL j (schedL tL))).
    exact (facts_scheduled_in_correspondence j _ _ (Hsched tR tL Ht)).
  Qed.

  Lemma facts_service_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel schedR schedL -> SubNatRel tR tL ->
    SubNatRel
      (@prosa.behavior.service.service_at Job stateR schedR j tR)
      (ImportedIdealUniExceedFacts.Prosa_Behavior_Service_service_at_inst4
        Job (iue_decidable_eq Job) stateL schedL j tL).
  Proof.
    intros Hsched Ht.
    change (SubNatRel
      (@prosa.behavior.schedule.service_in Job stateR j (schedR tR))
      (ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4
        Job (iue_decidable_eq Job) stateL j (schedL tL))).
    exact (facts_service_in_correspondence j _ _ (Hsched tR tL Ht)).
  Qed.

  Lemma facts_supply_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL)
      (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel schedR schedL -> SubNatRel tR tL ->
    SubNatRel
      (@prosa.model.processor.supply.supply_at Job stateR schedR tR)
      (ImportedIdealUniExceedFacts.Prosa_Model_Processor_Supply_supply_at_inst4
        Job (iue_decidable_eq Job) stateL schedL tL).
  Proof.
    intros Hsched Ht.
    change (SubNatRel
      (@prosa.behavior.schedule.supply_in Job stateR (schedR tR))
      (ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4
        Job (iue_decidable_eq Job) stateL (schedL tL))).
    exact (facts_supply_in_correspondence _ _ (Hsched tR tL Ht)).
  Qed.
End IdealUniExceedFactsOperations.

Print Assumptions facts_scheduled_in_correspondence.
Print Assumptions facts_supply_in_correspondence.
Print Assumptions facts_service_in_correspondence.
Print Assumptions facts_schedule_import.
Print Assumptions facts_schedule_export.
Print Assumptions facts_scheduled_at_correspondence.
Print Assumptions facts_service_at_correspondence.
Print Assumptions facts_supply_at_correspondence.
