From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.facts.model.ideal_uni_exceed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealUniExceedFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  IdealUniExceedFactsBaseAdapter IdealUniExceedFactsStateCorrespondence
  IdealUniExceedFactsSourceComputation IdealUniExceedFactsOperations.

Lemma facts_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P <-> Q) (ImportedIdealUniExceedFacts.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intro Hiff. apply ImportedIdealUniExceedFacts.Iff_intro.
    + intro HPL. exact (prop_to_sprop _ _ HQ
        (proj1 Hiff (sprop_to_prop _ _ HP HPL))).
    + intro HQL. exact (prop_to_sprop _ _ HP
        (proj2 Hiff (sprop_to_prop _ _ HQ HQL))).
  - intro Hiff. apply strictly_inhabits. split.
    + intro HPR. exact (sprop_to_prop _ _ HQ
        (ImportedIdealUniExceedFacts.Iff_mp _ _ Hiff
          (prop_to_sprop _ _ HP HPR))).
    + intro HQR. exact (sprop_to_prop _ _ HP
        (ImportedIdealUniExceedFacts.Iff_mpr _ _ Hiff
          (prop_to_sprop _ _ HQ HQR))).
Qed.

Section ScheduledStatement.
  Context (Job : eqType).
  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let stateL :=
    ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state
      Job (iue_decidable_eq Job).

  Lemma facts_state_or_correspondence
      (j : Job) (sR : IueSource Job) (sL : IueTarget Job) :
    IueRel Job sR sL ->
    PropSPropRel
      (sR = @prosa.model.processor.ideal_uni_exceed.NominalExecution Job j \/
       sR = @prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job j)
      (Lean.Or
        (Lean.eq sL
          (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution
            Job j))
        (Lean.eq sL
          (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution
            Job j))).
  Proof.
    intro Hstate.
    have Hnom := iue_equality_correspondence Job sR
      (@prosa.model.processor.ideal_uni_exceed.NominalExecution Job j)
      sL
      (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution
        Job j) Hstate (@Lean.eq_refl _ _).
    have Hexc := iue_equality_correspondence Job sR
      (@prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job j)
      sL
      (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution
        Job j) Hstate (@Lean.eq_refl _ _).
    apply prop_sprop_rel_intro.
    - intros [H|H].
      + apply Lean.Or_inl. exact (prop_to_sprop _ _ Hnom H).
      + apply Lean.Or_inr. exact (prop_to_sprop _ _ Hexc H).
    - intro H. destruct H as [H|H]; apply strictly_inhabits.
      + left. exact (sprop_to_prop _ _ Hnom H).
      + right. exact (sprop_to_prop _ _ Hexc H).
  Qed.

  Lemma facts_scheduled_statement_point
      (schedR : @prosa.behavior.schedule.schedule Job stateR)
      (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
        Job (iue_decidable_eq Job) stateL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    FactsScheduleRel Job schedR schedL -> SubNatRel tR tL ->
    PropSPropRel
      (@prosa.behavior.service.scheduled_at Job stateR schedR j tR <->
       schedR tR = @prosa.model.processor.ideal_uni_exceed.NominalExecution Job j \/
       schedR tR = @prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job j)
      (ImportedIdealUniExceedFacts.Iff
        (Lean.eq
          (ImportedIdealUniExceedFacts.Prosa_Behavior_Service_scheduled_at_inst4
            Job (iue_decidable_eq Job) stateL schedL j tL)
          ImportedIdealUniExceedFacts.Bool_true)
        (Lean.Or
          (Lean.eq (schedL tL)
            (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution
              Job j))
          (Lean.eq (schedL tL)
            (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution
              Job j)))).
  Proof.
    intros Hsched Ht.
    have Hscheduled := facts_scheduled_at_correspondence Job schedR schedL
      j tR tL Hsched Ht.
    have Hstates := facts_state_or_correspondence j (schedR tR)
      (schedL tL) (Hsched tR tL Ht).
    exact (facts_iff_correspondence _ _ _ _
      (iue_bool_truth_correspondence _ _ Hscheduled) Hstates).
  Qed.

  Lemma facts_scheduled_at_procstate_statement_correspondence :
    PropSPropRel
      (forall (schedR : @prosa.behavior.schedule.schedule Job stateR)
          (j : Job) (tR : nat),
        @prosa.behavior.service.scheduled_at Job stateR schedR j tR <->
        schedR tR = @prosa.model.processor.ideal_uni_exceed.NominalExecution Job j \/
        schedR tR = @prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job j)
      (forall (schedL : ImportedIdealUniExceedFacts.Prosa_Behavior_Schedule_schedule_inst4
          Job (iue_decidable_eq Job) stateL)
          (j : Job) (tL : Lean.Nat),
        ImportedIdealUniExceedFacts.Iff
          (Lean.eq
            (ImportedIdealUniExceedFacts.Prosa_Behavior_Service_scheduled_at_inst4
              Job (iue_decidable_eq Job) stateL schedL j tL)
            ImportedIdealUniExceedFacts.Bool_true)
          (Lean.Or
            (Lean.eq (schedL tL)
              (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution
                Job j))
            (Lean.eq (schedL tL)
              (ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution
                Job j)))).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource schedL j tL.
      pose (schedR := facts_schedule_to_source Job schedL).
      pose (tR := sub_nat_to_rocq tL).
      have Hpoint := facts_scheduled_statement_point schedR schedL j tR tL
        (facts_schedule_export Job schedL) (sub_nat_rel_surjective tL).
      exact (prop_to_sprop _ _ Hpoint (Hsource schedR j tR)).
    - intro Htarget. apply strictly_inhabits.
      intros schedR j tR.
      pose (schedL := facts_schedule_to_target Job schedR).
      pose (tL := sub_nat_to_imported tR).
      have Hpoint := facts_scheduled_statement_point schedR schedL j tR tL
        (facts_schedule_import Job schedR) (sub_nat_rel_canonical tR).
      exact (sprop_to_prop _ _ Hpoint (Htarget schedL j tL)).
  Qed.
End ScheduledStatement.

Print Assumptions facts_scheduled_at_procstate_statement_correspondence.
