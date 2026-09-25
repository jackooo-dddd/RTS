From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.facts.model.restricted_supply.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRestrictedSupplySchedule ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  RestrictedSupplyScheduleBaseAdapter RestrictedSupplyScheduleStateCorrespondence
  RestrictedSupplyScheduleSourceComputation RestrictedSupplyScheduleOperations.

Section RestrictedSupplyScheduleModelCorrespondence.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.restricted_supply.rs_processor_state Job.
  Let stateL :=
    ImportedRestrictedSupplySchedule.Prosa_Model_Processor_RestrictedSupply_rs_processor_state
      Job (rs_decidable_eq Job).

  Lemma facts_unit_supply_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job stateR)
      (ImportedRestrictedSupplySchedule.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4
        Job (rs_decidable_eq Job) stateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource sL.
      pose (sR := rs_to_source Job sL).
      have Hsupply := facts_supply_in_correspondence Job sR sL
        (rs_target_roundtrip Job sL).
      exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ 1 (sub_nat_to_imported 1)
          Hsupply (sub_nat_rel_canonical 1))
        (Hsource sR)).
    - intro Htarget. apply strictly_inhabits.
      intro sR.
      have Hsupply := facts_supply_in_correspondence Job sR
        (rs_to_target Job sR) (@Lean.eq_refl _ _).
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ 1 (sub_nat_to_imported 1)
          Hsupply (sub_nat_rel_canonical 1))
        (Htarget (rs_to_target Job sR))).
  Qed.

  Lemma facts_uniprocessor_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.uniprocessor_model
        Job stateR)
      (ImportedRestrictedSupplySchedule.Prosa_Model_Processor_PlatformProperties_uniprocessor_model_inst4
        Job (rs_decidable_eq Job) stateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j1 j2 schedL tL Htarget1 Htarget2.
      pose (schedR := facts_schedule_to_source Job schedL).
      pose (tR := sub_nat_to_rocq tL).
      have Hsched := facts_schedule_export Job schedL.
      have Ht := sub_nat_rel_surjective tL.
      have Hrel1 := facts_scheduled_at_correspondence Job schedR schedL
        j1 tR tL Hsched Ht.
      have Hrel2 := facts_scheduled_at_correspondence Job schedR schedL
        j2 tR tL Hsched Ht.
      have Hsource1 := sprop_to_prop _ _
        (rs_bool_truth_correspondence _ _ Hrel1) Htarget1.
      have Hsource2 := sprop_to_prop _ _
        (rs_bool_truth_correspondence _ _ Hrel2) Htarget2.
      exact (coq_eq_to_imported_eq j1 j2
        (Hsource j1 j2 schedR tR Hsource1 Hsource2)).
    - intro Htarget. apply strictly_inhabits.
      intros j1 j2 schedR tR Hsource1 Hsource2.
      pose (schedL := facts_schedule_to_target Job schedR).
      pose (tL := sub_nat_to_imported tR).
      have Hsched := facts_schedule_import Job schedR.
      have Ht := sub_nat_rel_canonical tR.
      have Hrel1 := facts_scheduled_at_correspondence Job schedR schedL
        j1 tR tL Hsched Ht.
      have Hrel2 := facts_scheduled_at_correspondence Job schedR schedL
        j2 tR tL Hsched Ht.
      have Htarget1 := prop_to_sprop _ _
        (rs_bool_truth_correspondence _ _ Hrel1) Hsource1.
      have Htarget2 := prop_to_sprop _ _
        (rs_bool_truth_correspondence _ _ Hrel2) Hsource2.
      exact (imported_eq_to_coq_eq j1 j2
        (Htarget j1 j2 schedL tL Htarget1 Htarget2)).
  Qed.

  Lemma facts_fully_consuming_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.fully_consuming_proc_model
        Job stateR)
      (ImportedRestrictedSupplySchedule.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4
        Job (rs_decidable_eq Job) stateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j schedL tL HtargetScheduled.
      pose (schedR := facts_schedule_to_source Job schedL).
      pose (tR := sub_nat_to_rocq tL).
      have Hsched := facts_schedule_export Job schedL.
      have Ht := sub_nat_rel_surjective tL.
      have Hscheduled := facts_scheduled_at_correspondence Job schedR schedL
        j tR tL Hsched Ht.
      have HsourceScheduled := sprop_to_prop _ _
        (rs_bool_truth_correspondence _ _ Hscheduled) HtargetScheduled.
      have Hservice := facts_service_at_correspondence Job schedR schedL
        j tR tL Hsched Ht.
      have Hsupply := facts_supply_at_correspondence Job schedR schedL
        tR tL Hsched Ht.
      exact (prop_to_sprop _ _
        (sub_nat_eq_correspondence _ _ _ _ Hservice Hsupply)
        (Hsource j schedR tR HsourceScheduled)).
    - intro Htarget. apply strictly_inhabits.
      intros j schedR tR HsourceScheduled.
      pose (schedL := facts_schedule_to_target Job schedR).
      pose (tL := sub_nat_to_imported tR).
      have Hsched := facts_schedule_import Job schedR.
      have Ht := sub_nat_rel_canonical tR.
      have Hscheduled := facts_scheduled_at_correspondence Job schedR schedL
        j tR tL Hsched Ht.
      have HtargetScheduled := prop_to_sprop _ _
        (rs_bool_truth_correspondence _ _ Hscheduled) HsourceScheduled.
      have Hservice := facts_service_at_correspondence Job schedR schedL
        j tR tL Hsched Ht.
      have Hsupply := facts_supply_at_correspondence Job schedR schedL
        tR tL Hsched Ht.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ _ _ Hservice Hsupply)
        (Htarget j schedL tL HtargetScheduled)).
  Qed.
End RestrictedSupplyScheduleModelCorrespondence.

Print Assumptions facts_unit_supply_model_correspondence.
Print Assumptions facts_uniprocessor_model_correspondence.
Print Assumptions facts_fully_consuming_model_correspondence.
