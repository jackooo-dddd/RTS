From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.facts.behavior.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsBehaviorSupply.
From FoundationCertificates Require Import PropSPropFoundation
  FsScheduleBaseAdapter FsScheduleCorrespondence
  FsProcessorStateCorrespondence FactsSupplyStatementCorrespondence.

(** Convertibility guards are separated from certificates.  The source guard
    consumes the pinned source theorem, while the target guard consumes the
    actual imported, statement-only Lean theorem.  Neither is used to prove
    the semantic correspondence. *)
Definition fs_source_of_relation {P : Prop} {Q : SProp}
    (_ : PropSPropRel P Q) : Prop := P.
Definition fs_target_of_relation {P : Prop} {Q : SProp}
    (_ : PropSPropRel P Q) : SProp := Q.

Section FactsSupplyExactTypeGuards.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedFactsBehaviorSupply.Prosa_Behavior_Schedule_ProcessorState
      Job (sch_decidable_eq Job).
  Variable R : SchProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL :
    ImportedFactsBehaviorSupply.Prosa_Behavior_Schedule_schedule
      Job (sch_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SchScheduleRel Job PStateR PStateL
      (sch_ps_state_rel Job PStateR PStateL R) schedR schedL.

  Definition fs_source_guard_service_at_le_supply_at :
    fs_source_of_relation (fs_service_at_le_supply_at_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    @prosa.analysis.facts.behavior.supply.service_at_le_supply_at
      Job PStateR schedR.
  Definition fs_target_guard_service_at_le_supply_at :
    fs_target_of_relation (fs_service_at_le_supply_at_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_service_at_le_supply_at
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_pos_service_impl_pos_supply :
    fs_source_of_relation (fs_pos_service_impl_pos_supply_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    @prosa.analysis.facts.behavior.supply.pos_service_impl_pos_supply
      Job PStateR schedR.
  Definition fs_target_guard_pos_service_impl_pos_supply :
    fs_target_of_relation (fs_pos_service_impl_pos_supply_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_pos_service_impl_pos_supply
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_blackout_or_supply :
    fs_source_of_relation (fs_blackout_or_supply_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    @prosa.analysis.facts.behavior.supply.blackout_or_supply
      Job PStateR schedR.
  Definition fs_target_guard_blackout_or_supply :
    fs_target_of_relation (fs_blackout_or_supply_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_blackout_or_supply
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_supply_at_complement :
    fs_source_of_relation (fs_supply_at_complement_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    fun H => @prosa.analysis.facts.behavior.supply.supply_at_complement
      Job PStateR H schedR.
  Definition fs_target_guard_supply_at_complement :
    fs_target_of_relation (fs_supply_at_complement_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_supply_at_complement
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_is_blackout_complement :
    fs_source_of_relation (fs_is_blackout_complement_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    fun H => @prosa.analysis.facts.behavior.supply.is_blackout_complement
      Job PStateR H schedR.
  Definition fs_target_guard_is_blackout_complement :
    fs_target_of_relation (fs_is_blackout_complement_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_is_blackout_complement
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_supply_at_le_1 :
    fs_source_of_relation (fs_supply_at_le_1_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    fun H => @prosa.analysis.facts.behavior.supply.supply_at_le_1
      Job PStateR H schedR.
  Definition fs_target_guard_supply_at_le_1 :
    fs_target_of_relation (fs_supply_at_le_1_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_supply_at_le_1
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_unit_supply_proc_service_case :
    fs_source_of_relation (fs_unit_supply_proc_service_case_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    fun H => @prosa.analysis.facts.behavior.supply.unit_supply_proc_service_case
      Job PStateR H schedR.
  Definition fs_target_guard_unit_supply_proc_service_case :
    fs_target_of_relation (fs_unit_supply_proc_service_case_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_unit_supply_proc_service_case
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_supply_during_bound :
    fs_source_of_relation (fs_supply_during_bound_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    fun H => @prosa.analysis.facts.behavior.supply.supply_during_bound
      Job PStateR H schedR.
  Definition fs_target_guard_supply_during_bound :
    fs_target_of_relation (fs_supply_during_bound_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_supply_during_bound
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_blackout_during_bound :
    fs_source_of_relation (fs_blackout_during_bound_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    @prosa.analysis.facts.behavior.supply.blackout_during_bound
      Job PStateR schedR.
  Definition fs_target_guard_blackout_during_bound :
    fs_target_of_relation (fs_blackout_during_bound_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_blackout_during_bound
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_supply_during_last_plus_before :
    fs_source_of_relation (fs_supply_during_last_plus_before_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    @prosa.analysis.facts.behavior.supply.supply_during_last_plus_before
      Job PStateR schedR.
  Definition fs_target_guard_supply_during_last_plus_before :
    fs_target_of_relation (fs_supply_during_last_plus_before_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_supply_during_last_plus_before
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_blackout_during_last_plus_before :
    fs_source_of_relation (fs_blackout_during_last_plus_before_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    @prosa.analysis.facts.behavior.supply.blackout_during_last_plus_before
      Job PStateR schedR.
  Definition fs_target_guard_blackout_during_last_plus_before :
    fs_target_of_relation (fs_blackout_during_last_plus_before_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_blackout_during_last_plus_before
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_supply_during_complement :
    fs_source_of_relation (fs_supply_during_complement_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    fun H => @prosa.analysis.facts.behavior.supply.supply_during_complement
      Job PStateR H schedR.
  Definition fs_target_guard_supply_during_complement :
    fs_target_of_relation (fs_supply_during_complement_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_supply_during_complement
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_blackout_during_complement :
    fs_source_of_relation (fs_blackout_during_complement_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    fun H => @prosa.analysis.facts.behavior.supply.blackout_during_complement
      Job PStateR H schedR.
  Definition fs_target_guard_blackout_during_complement :
    fs_target_of_relation (fs_blackout_during_complement_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_blackout_during_complement
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_blackout_during_cat :
    fs_source_of_relation (fs_blackout_during_cat_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    @prosa.analysis.facts.behavior.supply.blackout_during_cat
      Job PStateR schedR.
  Definition fs_target_guard_blackout_during_cat :
    fs_target_of_relation (fs_blackout_during_cat_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_blackout_during_cat
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_blackout_during_unit_growth :
    fs_source_of_relation (fs_blackout_during_unit_growth_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    @prosa.analysis.facts.behavior.supply.blackout_during_unit_growth
      Job PStateR schedR.
  Definition fs_target_guard_blackout_during_unit_growth :
    fs_target_of_relation (fs_blackout_during_unit_growth_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_blackout_during_unit_growth
      Job (sch_decidable_eq Job) PStateL schedL.

  Definition fs_source_guard_progress_inside_supplies :
    fs_source_of_relation (fs_progress_inside_supplies_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    fun H => @prosa.analysis.facts.behavior.supply.progress_inside_supplies
      Job PStateR H schedR.
  Definition fs_target_guard_progress_inside_supplies :
    fs_target_of_relation (fs_progress_inside_supplies_correspondence
      Job PStateR PStateL R schedR schedL Hsched) :=
    ImportedFactsBehaviorSupply.Prosa_Analysis_Facts_Behavior_Supply_progress_inside_supplies
      Job (sch_decidable_eq Job) PStateL schedL.

End FactsSupplyExactTypeGuards.
