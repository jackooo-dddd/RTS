From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsBehaviorSupply
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence FsScheduleBaseAdapter
  FsScheduleFiniteOperations FsScheduleCorrespondence
  FsProcessorStateCorrespondence.

(** Target-local replay of the two accepted PlatformProperties observations
    used by [analysis/facts/behavior/supply.v].  No source/target theorem
    proof from that facts file occurs in either proof. *)

Section FactsPlatformProperties.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedFactsBehaviorSupply.Prosa_Behavior_Schedule_ProcessorState
      Job (sch_decidable_eq Job).
  Variable R : SchProcessorStateRel Job PStateR PStateL.

  Let stateToR := sch_ps_state_to_source Job PStateR PStateL R.
  Let stateToL := sch_ps_state_to_target Job PStateR PStateL R.
  Let stateSurj := sch_ps_state_rel_surjective Job PStateR PStateL R.
  Let stateCanonical := sch_ps_state_rel_canonical Job PStateR PStateL R.

  Lemma fs_unit_supply_proc_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR)
      (ImportedFactsBehaviorSupply.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
        Job (sch_decidable_eq Job) PStateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource sL.
      pose (sR := stateToR sL).
      have Hstate := stateSurj sL.
      have Hsupply := supply_in_certificate Job PStateR PStateL R
        sR sL Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ 1 (sub_nat_to_imported 1)
          Hsupply (sub_nat_rel_canonical 1))
        (Hsource sR)).
    - intro Htarget. apply strictly_inhabits.
      intro sR.
      have Hstate := stateCanonical sR.
      have Hsupply := supply_in_certificate Job PStateR PStateL R
        sR (stateToL sR) Hstate.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ 1 (sub_nat_to_imported 1)
          Hsupply (sub_nat_rel_canonical 1))
        (Htarget (stateToL sR))).
  Qed.

  Lemma fs_fully_consuming_proc_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.fully_consuming_proc_model
        Job PStateR)
      (ImportedFactsBehaviorSupply.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model
        Job (sch_decidable_eq Job) PStateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j schedL tL HtargetScheduled.
      pose (schedR := export_schedule Job PStateR PStateL stateToR schedL).
      pose (tR := sub_nat_to_rocq tL).
      have Hsched := schedule_export_certificate Job PStateR PStateL R
        schedL.
      have Hstate := Hsched tR tL (sub_nat_rel_surjective tL).
      have Hscheduled := scheduled_in_certificate Job PStateR PStateL R
        j (schedR tR) (schedL tL) Hstate.
      have HsourceScheduled := sprop_to_prop _ _
        (sch_bool_truth_correspondence _ _ Hscheduled) HtargetScheduled.
      have Hservice := service_in_certificate Job PStateR PStateL R
        j (schedR tR) (schedL tL) Hstate.
      have Hsupply := supply_in_certificate Job PStateR PStateL R
        (schedR tR) (schedL tL) Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_eq_correspondence _ _ _ _ Hservice Hsupply)
        (Hsource j schedR tR HsourceScheduled)).
    - intro Htarget. apply strictly_inhabits.
      intros j schedR tR HsourceScheduled.
      pose (schedL := import_schedule Job PStateR PStateL stateToL schedR).
      pose (tL := sub_nat_to_imported tR).
      have Hsched := schedule_import_certificate Job PStateR PStateL R
        schedR.
      have Hstate := Hsched tR tL (sub_nat_rel_canonical tR).
      have Hscheduled := scheduled_in_certificate Job PStateR PStateL R
        j (schedR tR) (schedL tL) Hstate.
      have HtargetScheduled := prop_to_sprop _ _
        (sch_bool_truth_correspondence _ _ Hscheduled) HsourceScheduled.
      have Hservice := service_in_certificate Job PStateR PStateL R
        j (schedR tR) (schedL tL) Hstate.
      have Hsupply := supply_in_certificate Job PStateR PStateL R
        (schedR tR) (schedL tL) Hstate.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ _ _ Hservice Hsupply)
        (Htarget j schedL tL HtargetScheduled)).
  Qed.
End FactsPlatformProperties.

Print Assumptions fs_unit_supply_proc_model_correspondence.
Print Assumptions fs_fully_consuming_proc_model_correspondence.
