From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.facts.model.ideal_uni_exceed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealUniExceedFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  IdealUniExceedFactsBaseAdapter IdealUniExceedFactsStateCorrespondence
  IdealUniExceedFactsSourceComputation IdealUniExceedFactsOperations
  IdealUniExceedFactsCorrespondence.

Section BlackoutStatement.
  Context (Job : eqType).
  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let stateL :=
    ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state
      Job (iue_decidable_eq Job).

  Definition facts_target_supply_in (sL : IueTarget Job) : Lean.Nat :=
    ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4
      Job (iue_decidable_eq Job) stateL sL.

  Definition facts_target_blackout_state (sL : IueTarget Job) :
      ImportedIdealUniExceedFacts.Bool :=
    ImportedIdealUniExceedFacts.Bool_not
      (ImportedIdealUniExceedFacts.Decidable_decide
        (ImportedIdealUniExceedFacts.LT_lt_inst1 Lean.Nat
          ImportedIdealUniExceedFacts.instLTNat Lean.Nat_zero
          (facts_target_supply_in sL))
        (ImportedIdealUniExceedFacts.Nat_decLt Lean.Nat_zero
          (facts_target_supply_in sL))).

  Lemma facts_blackout_state_canonical (sR : IueSource Job) :
    IueBoolRel
      (~~ (@prosa.behavior.schedule.supply_in Job stateR sR > 0))
      (facts_target_blackout_state (iue_to_target Job sR)).
  Proof.
    rewrite (facts_source_supply_in_concrete Job sR).
    unfold facts_target_blackout_state, facts_target_supply_in.
    destruct (ImportedIdealUniExceedFacts.Prosa_Validation_IdealUniExceedFactsInterface_production_supply_in_concrete
      Job (iue_decidable_eq Job) (iue_to_target Job sR)).
    destruct sR; cbn; exact (@Lean.eq_refl _ _).
  Qed.

  Lemma facts_blackout_state_correspondence
      (sR : IueSource Job) (sL : IueTarget Job) :
    IueRel Job sR sL ->
    IueBoolRel
      (~~ (@prosa.behavior.schedule.supply_in Job stateR sR > 0))
      (facts_target_blackout_state sL).
  Proof.
    intro Hstate. destruct Hstate.
    exact (facts_blackout_state_canonical sR).
  Qed.

  Lemma facts_blackout_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL)
      (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel Job schedR schedL -> SubNatRel tR tL ->
    IueBoolRel
      (@prosa.model.processor.supply.is_blackout Job stateR schedR tR)
      (ImportedIdealUniExceedFacts.Prosa_Model_Processor_Supply_is_blackout_inst4
        Job (iue_decidable_eq Job) stateL schedL tL).
  Proof.
    intros Hsched Ht.
    have Hstate := facts_blackout_state_correspondence
      (schedR tR) (schedL tL) (Hsched tR tL Ht).
    have Htarget :=
      ImportedIdealUniExceedFacts.Prosa_Validation_IdealUniExceedFactsInterface_production_is_blackout_eq
        Job (iue_decidable_eq Job) schedL tL.
    change (IueBoolRel
      (~~ (@prosa.behavior.schedule.supply_in Job stateR (schedR tR) > 0))
      (ImportedIdealUniExceedFacts.Prosa_Model_Processor_Supply_is_blackout_inst4
        Job (iue_decidable_eq Job) stateL schedL tL)).
    exact (sub_imported_eq_trans _ _ _ Hstate
      (sub_imported_eq_sym _ _ Htarget)).
  Qed.

  Lemma facts_is_exceedance_exec_at_correspondence
      (sR : IueSource Job) (sL : IueTarget Job) :
    IueRel Job sR sL ->
    IueBoolRel
      (@prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec Job sR)
      (ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec
        Job (iue_decidable_eq Job) sL).
  Proof.
    intro Hstate. destruct Hstate.
    exact (facts_is_exceedance_exec_correspondence Job sR).
  Qed.

  Lemma facts_bool_equality_correspondence
      (aR bR : bool) (aL bL : ImportedIdealUniExceedFacts.Bool) :
    IueBoolRel aR aL -> IueBoolRel bR bL ->
    PropSPropRel (aR = bR) (Lean.eq aL bL).
  Proof.
    intros Ha Hb. apply prop_sprop_rel_intro.
    - intro Hab. destruct Hab. destruct Ha. destruct Hb.
      exact (@Lean.eq_refl _ _).
    - intro Hab. apply strictly_inhabits.
      destruct Ha. destruct Hb.
      have Hdecoded := f_equal iue_bool_to_rocq
        (imported_eq_to_coq_eq _ _ Hab).
      rewrite (iue_bool_source_roundtrip aR)
        (iue_bool_source_roundtrip bR) in Hdecoded.
      exact Hdecoded.
  Qed.

  Lemma facts_blackout_statement_point
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL)
      (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel Job schedR schedL -> SubNatRel tR tL ->
    PropSPropRel
      (@prosa.model.processor.supply.is_blackout Job stateR schedR tR =
        @prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec
          Job (schedR tR))
      (Lean.eq
        (ImportedIdealUniExceedFacts.Prosa_Model_Processor_Supply_is_blackout_inst4
          Job (iue_decidable_eq Job) stateL schedL tL)
        (ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec
          Job (iue_decidable_eq Job) (schedL tL))).
  Proof.
    intros Hsched Ht.
    have Hblack := facts_blackout_at_correspondence schedR schedL tR tL
      Hsched Ht.
    have Hexec := facts_is_exceedance_exec_at_correspondence
      (schedR tR) (schedL tL) (Hsched tR tL Ht).
    exact (facts_bool_equality_correspondence _ _ _ _ Hblack Hexec).
  Qed.

  Lemma facts_blackout_statement_correspondence :
    PropSPropRel
      (forall (schedR : @prosa.behavior.schedule.schedule Job stateR)
          (tR : nat),
        @prosa.model.processor.supply.is_blackout Job stateR schedR tR =
        @prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec
          Job (schedR tR))
      (forall (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
          Job (iue_decidable_eq Job) stateL)
          (tL : Lean.Nat),
        Lean.eq
          (ImportedIdealUniExceedFacts.Prosa_Model_Processor_Supply_is_blackout_inst4
            Job (iue_decidable_eq Job) stateL schedL tL)
          (ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec
            Job (iue_decidable_eq Job) (schedL tL))).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource schedL tL.
      pose (schedR := facts_schedule_to_source Job schedL).
      pose (tR := sub_nat_to_rocq tL).
      have Hpoint := facts_blackout_statement_point schedR schedL tR tL
        (facts_schedule_export Job schedL) (sub_nat_rel_surjective tL).
      exact (prop_to_sprop _ _ Hpoint (Hsource schedR tR)).
    - intro Htarget. apply strictly_inhabits.
      intros schedR tR.
      pose (schedL := facts_schedule_to_target Job schedR).
      pose (tL := sub_nat_to_imported tR).
      have Hpoint := facts_blackout_statement_point schedR schedL tR tL
        (facts_schedule_import Job schedR) (sub_nat_rel_canonical tR).
      exact (sprop_to_prop _ _ Hpoint (Htarget schedL tL)).
  Qed.
End BlackoutStatement.

Print Assumptions facts_blackout_state_canonical.
Print Assumptions facts_blackout_state_correspondence.
Print Assumptions facts_blackout_at_correspondence.
Print Assumptions facts_bool_equality_correspondence.
Print Assumptions facts_blackout_statement_correspondence.
