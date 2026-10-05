(* Re-bound copy of the accepted platform_properties PlatformPropertiesCorrespondence.v for the
   uniprocessor artifact; only module names differ. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import
  ImportedUniprocessor ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  UniPlatformScheduleBaseAdapter UniPlatformScheduleFiniteOperations
  UniPlatformScheduleCorrespondence UniPlatformProcessorStateCorrespondence.

(** The processor-state relation is the previously certified, two-sided
    observational representation relation, recompiled against this exact
    imported artifact.  These certificates never invoke either theorem proof. *)

Section UniPlatformPropertiesCorrespondence.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState
      Job (sch_decidable_eq Job).
  Variable R : SchProcessorStateRel Job PStateR PStateL.

  Let stateToR := sch_ps_state_to_source Job PStateR PStateL R.
  Let stateToL := sch_ps_state_to_target Job PStateR PStateL R.
  Let stateSurj := sch_ps_state_rel_surjective Job PStateR PStateL R.
  Let stateCanonical := sch_ps_state_rel_canonical Job PStateR PStateL R.

  Lemma unit_service_proc_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_service_proc_model
        Job PStateR)
      (ImportedUniprocessor.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model
        Job (sch_decidable_eq Job) PStateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL.
      pose (sR := stateToR sL).
      have Hstate := stateSurj sL.
      have Hservice := service_in_certificate Job PStateR PStateL R
        j sR sL Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ 1 (sub_nat_to_imported 1)
          Hservice (sub_nat_rel_canonical 1))
        (Hsource j sR)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR.
      have Hstate := stateCanonical sR.
      have Hservice := service_in_certificate Job PStateR PStateL R
        j sR (stateToL sR) Hstate.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ 1 (sub_nat_to_imported 1)
          Hservice (sub_nat_rel_canonical 1))
        (Htarget j (stateToL sR))).
  Qed.

  Lemma unit_supply_proc_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR)
      (ImportedUniprocessor.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
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

  Lemma ideal_progress_proc_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.ideal_progress_proc_model
        Job PStateR)
      (ImportedUniprocessor.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model
        Job (sch_decidable_eq Job) PStateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL HtargetScheduled.
      pose (sR := stateToR sL).
      have Hstate := stateSurj sL.
      have Hscheduled := scheduled_in_certificate Job PStateR PStateL R
        j sR sL Hstate.
      have HsourceScheduled := sprop_to_prop _ _
        (sch_bool_truth_correspondence _ _ Hscheduled) HtargetScheduled.
      have Hservice := service_in_certificate Job PStateR PStateL R
        j sR sL Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_lt_correspondence 0 (sub_nat_to_imported 0)
          _ _ (sub_nat_rel_canonical 0) Hservice)
        (Hsource j sR HsourceScheduled)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR HsourceScheduled.
      have Hstate := stateCanonical sR.
      have Hscheduled := scheduled_in_certificate Job PStateR PStateL R
        j sR (stateToL sR) Hstate.
      have HtargetScheduled := prop_to_sprop _ _
        (sch_bool_truth_correspondence _ _ Hscheduled) HsourceScheduled.
      have Hservice := service_in_certificate Job PStateR PStateL R
        j sR (stateToL sR) Hstate.
      exact (sprop_to_prop _ _
        (sub_nat_lt_correspondence 0 (sub_nat_to_imported 0)
          _ _ (sub_nat_rel_canonical 0) Hservice)
        (Htarget j (stateToL sR) HtargetScheduled)).
  Qed.

  Lemma uniprocessor_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.uniprocessor_model
        Job PStateR)
      (ImportedUniprocessor.Prosa_Model_Processor_PlatformProperties_uniprocessor_model
        Job (sch_decidable_eq Job) PStateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j1 j2 schedL tL Htarget1 Htarget2.
      pose (schedR := export_schedule Job PStateR PStateL stateToR schedL).
      pose (tR := sub_nat_to_rocq tL).
      have Hsched := schedule_export_certificate Job PStateR PStateL R
        schedL.
      have Hstate := Hsched tR tL (sub_nat_rel_surjective tL).
      have Hrel1 := scheduled_in_certificate Job PStateR PStateL R
        j1 (schedR tR) (schedL tL) Hstate.
      have Hrel2 := scheduled_in_certificate Job PStateR PStateL R
        j2 (schedR tR) (schedL tL) Hstate.
      have Hsource1 := sprop_to_prop _ _
        (sch_bool_truth_correspondence _ _ Hrel1) Htarget1.
      have Hsource2 := sprop_to_prop _ _
        (sch_bool_truth_correspondence _ _ Hrel2) Htarget2.
      exact (coq_eq_to_imported_eq j1 j2
        (Hsource j1 j2 schedR tR Hsource1 Hsource2)).
    - intro Htarget. apply strictly_inhabits.
      intros j1 j2 schedR tR Hsource1 Hsource2.
      pose (schedL := import_schedule Job PStateR PStateL stateToL schedR).
      pose (tL := sub_nat_to_imported tR).
      have Hsched := schedule_import_certificate Job PStateR PStateL R
        schedR.
      have Hstate := Hsched tR tL (sub_nat_rel_canonical tR).
      have Hrel1 := scheduled_in_certificate Job PStateR PStateL R
        j1 (schedR tR) (schedL tL) Hstate.
      have Hrel2 := scheduled_in_certificate Job PStateR PStateL R
        j2 (schedR tR) (schedL tL) Hstate.
      have Htarget1 := prop_to_sprop _ _
        (sch_bool_truth_correspondence _ _ Hrel1) Hsource1.
      have Htarget2 := prop_to_sprop _ _
        (sch_bool_truth_correspondence _ _ Hrel2) Hsource2.
      exact (imported_eq_to_coq_eq j1 j2
        (Htarget j1 j2 schedL tL Htarget1 Htarget2)).
  Qed.

  Lemma fully_consuming_proc_model_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.fully_consuming_proc_model
        Job PStateR)
      (ImportedUniprocessor.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model
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

  Lemma unit_supply_is_unit_service_statement_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR ->
       @prosa.model.processor.platform_properties.unit_service_proc_model
        Job PStateR)
      (ImportedUniprocessor.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
        Job (sch_decidable_eq Job) PStateL ->
       ImportedUniprocessor.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model
        Job (sch_decidable_eq Job) PStateL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource HtargetSupply.
      apply (prop_to_sprop _ _ unit_service_proc_model_correspondence).
      apply Hsource.
      exact (sprop_to_prop _ _ unit_supply_proc_model_correspondence
        HtargetSupply).
    - intro Htarget. apply strictly_inhabits.
      intro HsourceSupply.
      apply (sprop_to_prop _ _ unit_service_proc_model_correspondence).
      apply Htarget.
      exact (prop_to_sprop _ _ unit_supply_proc_model_correspondence
        HsourceSupply).
  Qed.
End UniPlatformPropertiesCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN platform_unit_service". exact I. Qed.
Print Assumptions unit_service_proc_model_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END platform_unit_service". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN platform_ideal_progress". exact I. Qed.
Print Assumptions ideal_progress_proc_model_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END platform_ideal_progress". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN platform_uniprocessor". exact I. Qed.
Print Assumptions uniprocessor_model_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END platform_uniprocessor". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN platform_unit_supply". exact I. Qed.
Print Assumptions unit_supply_proc_model_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END platform_unit_supply". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN platform_unit_supply_implies_service". exact I. Qed.
Print Assumptions unit_supply_is_unit_service_statement_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END platform_unit_supply_implies_service". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN platform_fully_consuming". exact I. Qed.
Print Assumptions fully_consuming_proc_model_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END platform_fully_consuming". exact I. Qed.
