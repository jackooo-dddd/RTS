From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSchedule ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ScheduleBaseAdapter
  ScheduleFiniteOperations ScheduleCorrespondence.

(** Full observational relation for the v0.6 ProcessorState abstraction.
    The two carrier types need not be definitionally identical.  The witness
    records bidirectional carrier maps, roundtrips, the finite enumeration
    relation, and every observable class field. *)

Section ProcessorStateRelation.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let CoreR : finType := @prosa.behavior.schedule.Core Job PStateR.
  Let StateL : Type :=
    ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State Job
      (sch_decidable_eq Job) PStateL.
  Let CoreL : Type :=
    ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_Core Job
      (sch_decidable_eq Job) PStateL.

  Definition sch_ps_target_scheduled_on (j : Job) (s : StateL)
      (c : CoreL) : ImportedSchedule.Bool :=
    ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_on
      Job (sch_decidable_eq Job) PStateL j s c.

  Definition sch_ps_target_supply_on (s : StateL) (c : CoreL) : Lean.Nat :=
    ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_supply_on
      Job (sch_decidable_eq Job) PStateL s c.

  Definition sch_ps_target_service_on (j : Job) (s : StateL)
      (c : CoreL) : Lean.Nat :=
    ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_service_on
      Job (sch_decidable_eq Job) PStateL j s c.

  Record SchProcessorStateRel : Type := {
    sch_ps_state_rel : StateR -> StateL -> SProp;
    sch_ps_state_to_target : StateR -> StateL;
    sch_ps_state_to_source : StateL -> StateR;
    sch_ps_core_to_target : CoreR -> CoreL;
    sch_ps_core_to_source : CoreL -> CoreR;

    sch_ps_state_source_roundtrip : forall sR,
      Logic.eq (sch_ps_state_to_source (sch_ps_state_to_target sR)) sR;
    sch_ps_state_target_roundtrip : forall sL,
      Lean.eq (sch_ps_state_to_target (sch_ps_state_to_source sL)) sL;
    sch_ps_core_source_roundtrip : forall cR,
      Logic.eq (sch_ps_core_to_source (sch_ps_core_to_target cR)) cR;
    sch_ps_core_target_roundtrip : forall cL,
      Lean.eq (sch_ps_core_to_target (sch_ps_core_to_source cL)) cL;

    sch_ps_state_rel_canonical : forall sR,
      sch_ps_state_rel sR (sch_ps_state_to_target sR);
    sch_ps_state_rel_surjective : forall sL,
      sch_ps_state_rel (sch_ps_state_to_source sL) sL;

    sch_ps_core_enumeration_rel :
      SchCoreEnumerationRel CoreR CoreL sch_ps_core_to_target
        (ImportedSchedule.Prosa_Validation_ScheduleInterface_coreEnumeration
          Job (sch_decidable_eq Job) PStateL);

    sch_ps_scheduled_on_rel :
      forall (j : Job) (sR : StateR) (sL : StateL) (cR : CoreR),
        sch_ps_state_rel sR sL ->
        SchBoolRel (@prosa.behavior.schedule.scheduled_on Job PStateR
            j sR cR)
          (sch_ps_target_scheduled_on j sL
            (sch_ps_core_to_target cR));

    sch_ps_supply_on_rel :
      forall (sR : StateR) (sL : StateL) (cR : CoreR),
        sch_ps_state_rel sR sL ->
        SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
          (sch_ps_target_supply_on sL (sch_ps_core_to_target cR));

    sch_ps_service_on_rel :
      forall (j : Job) (sR : StateR) (sL : StateL) (cR : CoreR),
        sch_ps_state_rel sR sL ->
        SubNatRel (@prosa.behavior.schedule.service_on Job PStateR
            j sR cR)
          (sch_ps_target_service_on j sL
            (sch_ps_core_to_target cR))
  }.

  Variable R : SchProcessorStateRel.

  Definition sch_source_supply_bound_law : Prop :=
    forall (j : Job) (s : StateR) (c : CoreR),
      is_true (leq
        (@prosa.behavior.schedule.service_on Job PStateR j s c)
        (@prosa.behavior.schedule.supply_on Job PStateR s c)).

  Definition sch_target_supply_bound_law : SProp :=
    forall (j : Job) (s : StateL) (c : CoreL),
      ImportedSchedule.LE_le_inst1 Lean.Nat ImportedSchedule.instLENat
        (sch_ps_target_service_on j s c)
        (sch_ps_target_supply_on s c).

  Definition sch_source_service_requires_schedule_law : Prop :=
    forall (j : Job) (s : StateR) (c : CoreR),
      is_true (~~ @prosa.behavior.schedule.scheduled_on Job PStateR j s c) ->
      Logic.eq (@prosa.behavior.schedule.service_on Job PStateR j s c) O.

  Definition sch_target_service_requires_schedule_law : SProp :=
    forall (j : Job) (s : StateL) (c : CoreL),
      Lean.eq (sch_ps_target_scheduled_on j s c)
        ImportedSchedule.Bool_false ->
      Lean.eq (sch_ps_target_service_on j s c) sch_target_zero.

  Lemma sch_ps_scheduled_at_target_core (j : Job)
      (sR : StateR) (sL : StateL) (cL : CoreL) :
    sch_ps_state_rel R sR sL ->
    SchBoolRel (@prosa.behavior.schedule.scheduled_on Job PStateR
        j sR (sch_ps_core_to_source R cL))
      (sch_ps_target_scheduled_on j sL cL).
  Proof.
    intro Hstate. apply (sch_bool_rel_target_transport _
      (sch_ps_target_scheduled_on j sL
        (sch_ps_core_to_target R (sch_ps_core_to_source R cL))) _).
    - exact (sch_ps_scheduled_on_rel R j sR sL
        (sch_ps_core_to_source R cL) Hstate).
    - exact (sub_imported_eq_congr (sch_ps_target_scheduled_on j sL)
        _ _ (sch_ps_core_target_roundtrip R cL)).
  Qed.

  Lemma sch_ps_supply_at_target_core (sR : StateR)
      (sL : StateL) (cL : CoreL) :
    sch_ps_state_rel R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR
        sR (sch_ps_core_to_source R cL))
      (sch_ps_target_supply_on sL cL).
  Proof.
    intro Hstate. apply (sch_nat_rel_target_transport _
      (sch_ps_target_supply_on sL
        (sch_ps_core_to_target R (sch_ps_core_to_source R cL))) _).
    - exact (sch_ps_supply_on_rel R sR sL
        (sch_ps_core_to_source R cL) Hstate).
    - exact (sub_imported_eq_congr (sch_ps_target_supply_on sL)
        _ _ (sch_ps_core_target_roundtrip R cL)).
  Qed.

  Lemma sch_ps_service_at_target_core (j : Job)
      (sR : StateR) (sL : StateL) (cL : CoreL) :
    sch_ps_state_rel R sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_on Job PStateR
        j sR (sch_ps_core_to_source R cL))
      (sch_ps_target_service_on j sL cL).
  Proof.
    intro Hstate. apply (sch_nat_rel_target_transport _
      (sch_ps_target_service_on j sL
        (sch_ps_core_to_target R (sch_ps_core_to_source R cL))) _).
    - exact (sch_ps_service_on_rel R j sR sL
        (sch_ps_core_to_source R cL) Hstate).
    - exact (sub_imported_eq_congr (sch_ps_target_service_on j sL)
        _ _ (sch_ps_core_target_roundtrip R cL)).
  Qed.

  Lemma processor_state_supply_bound_law_correspondence :
    PropSPropRel sch_source_supply_bound_law
      sch_target_supply_bound_law.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL cL.
      have Hstate := sch_ps_state_rel_surjective R sL.
      have Hservice := sch_ps_service_at_target_core j
        (sch_ps_state_to_source R sL) sL cL Hstate.
      have Hsupply := sch_ps_supply_at_target_core
        (sch_ps_state_to_source R sL) sL cL Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ _ _ Hservice Hsupply)
        (Hsource j (sch_ps_state_to_source R sL)
          (sch_ps_core_to_source R cL))).
    - intro Htarget. apply strictly_inhabits.
      intros j sR cR.
      have Hstate := sch_ps_state_rel_canonical R sR.
      have Hservice := sch_ps_service_on_rel R j sR
        (sch_ps_state_to_target R sR) cR Hstate.
      have Hsupply := sch_ps_supply_on_rel R sR
        (sch_ps_state_to_target R sR) cR Hstate.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ _ _ Hservice Hsupply)
        (Htarget j (sch_ps_state_to_target R sR)
          (sch_ps_core_to_target R cR))).
  Qed.

  Lemma sch_bool_false_correspondence bR bL :
    SchBoolRel bR bL ->
    PropSPropRel (is_true (~~ bR))
      (Lean.eq bL ImportedSchedule.Bool_false).
  Proof.
    intro Hrel. apply prop_sprop_rel_intro.
    - intro Hfalse. destruct bR, bL; cbn in *.
      + discriminate Hfalse.
      + discriminate Hfalse.
      + exact (@Lean.eq_refl _ _).
      + exact (sch_false_elim _ (sch_false_ne_true Hrel)).
    - intro Hfalse. destruct bR, bL; cbn in *.
      + exact (sch_false_elim _ (sch_false_ne_true
          (sub_imported_eq_sym _ _ Hrel))).
      + exact (sch_false_elim _ (sch_false_ne_true
          (sub_imported_eq_sym _ _ Hfalse))).
      + exact (strictly_inhabits (Logic.eq_refl true)).
      + exact (sch_false_elim _ (sch_false_ne_true Hrel)).
  Qed.

  Lemma processor_state_service_rule_correspondence :
    PropSPropRel sch_source_service_requires_schedule_law
      sch_target_service_requires_schedule_law.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL cL HnotScheduled.
      have Hstate := sch_ps_state_rel_surjective R sL.
      have Hscheduled := sch_ps_scheduled_at_target_core j
        (sch_ps_state_to_source R sL) sL cL Hstate.
      have Hservice := sch_ps_service_at_target_core j
        (sch_ps_state_to_source R sL) sL cL Hstate.
      have HsourceNot := sprop_to_prop _ _
        (sch_bool_false_correspondence _ _ Hscheduled) HnotScheduled.
      exact (prop_to_sprop _ _
        (sub_nat_eq_correspondence _ _ O sch_target_zero
          Hservice (sub_nat_rel_canonical O))
        (Hsource j (sch_ps_state_to_source R sL)
          (sch_ps_core_to_source R cL) HsourceNot)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR cR HnotScheduled.
      have Hstate := sch_ps_state_rel_canonical R sR.
      have Hscheduled := sch_ps_scheduled_on_rel R j sR
        (sch_ps_state_to_target R sR) cR Hstate.
      have Hservice := sch_ps_service_on_rel R j sR
        (sch_ps_state_to_target R sR) cR Hstate.
      have HtargetNot := prop_to_sprop _ _
        (sch_bool_false_correspondence _ _ Hscheduled) HnotScheduled.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ O sch_target_zero
          Hservice (sub_nat_rel_canonical O))
        (Htarget j (sch_ps_state_to_target R sR)
          (sch_ps_core_to_target R cR) HtargetNot)).
  Qed.

  Theorem processor_state_observational_correspondence :
    PropSPropRel sch_source_supply_bound_law
      sch_target_supply_bound_law /\
    PropSPropRel sch_source_service_requires_schedule_law
      sch_target_service_requires_schedule_law.
  Proof.
    split.
    - exact processor_state_supply_bound_law_correspondence.
    - exact processor_state_service_rule_correspondence.
  Qed.

  Theorem scheduled_in_certificate (j : Job)
      (sR : StateR) (sL : StateL) :
    sch_ps_state_rel R sR sL ->
    SchBoolRel (@prosa.behavior.schedule.scheduled_in Job PStateR j sR)
      (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
        Job (sch_decidable_eq Job) PStateL j sL).
  Proof.
    exact (scheduled_in_correspondence Job PStateR PStateL
      (sch_ps_state_rel R)
      (sch_ps_core_to_target R) (sch_ps_core_to_source R)
      (sch_ps_core_target_roundtrip R)
      (sch_ps_scheduled_on_rel R) j sR sL).
  Qed.

  Theorem supply_in_certificate (sR : StateR) (sL : StateL) :
    sch_ps_state_rel R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_in Job PStateR sR)
      (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_supply_in
        Job (sch_decidable_eq Job) PStateL sL).
  Proof.
    exact (supply_in_correspondence Job PStateR PStateL
      (sch_ps_state_rel R)
      (sch_ps_core_to_target R)
      (sch_ps_supply_on_rel R) (sch_ps_core_enumeration_rel R) sR sL).
  Qed.

  Theorem service_in_certificate (j : Job)
      (sR : StateR) (sL : StateL) :
    sch_ps_state_rel R sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_in Job PStateR j sR)
      (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_service_in
        Job (sch_decidable_eq Job) PStateL j sL).
  Proof.
    exact (service_in_correspondence Job PStateR PStateL
      (sch_ps_state_rel R)
      (sch_ps_core_to_target R)
      (sch_ps_service_on_rel R) (sch_ps_core_enumeration_rel R) j sR sL).
  Qed.

  Theorem schedule_import_certificate
      (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
    SchScheduleRel Job PStateR PStateL (sch_ps_state_rel R)
      schedR
      (import_schedule Job PStateR PStateL
        (sch_ps_state_to_target R) schedR).
  Proof.
    exact (schedule_import_correspondence Job PStateR PStateL
      (sch_ps_state_rel R)
      (sch_ps_state_to_target R)
      (sch_ps_state_rel_canonical R) schedR).
  Qed.

  Theorem schedule_export_certificate
      (schedL : ImportedSchedule.Prosa_Behavior_Schedule_schedule Job
        (sch_decidable_eq Job) PStateL) :
    SchScheduleRel Job PStateR PStateL (sch_ps_state_rel R)
      (export_schedule Job PStateR PStateL
        (sch_ps_state_to_source R) schedL) schedL.
  Proof.
    exact (schedule_export_correspondence Job PStateR PStateL
      (sch_ps_state_rel R)
      (sch_ps_state_to_source R)
      (sch_ps_state_rel_surjective R) schedL).
  Qed.

End ProcessorStateRelation.

Print Assumptions processor_state_observational_correspondence.
Print Assumptions scheduled_in_certificate.
Print Assumptions supply_in_certificate.
Print Assumptions service_in_certificate.
Print Assumptions schedule_import_certificate.
Print Assumptions schedule_export_certificate.
