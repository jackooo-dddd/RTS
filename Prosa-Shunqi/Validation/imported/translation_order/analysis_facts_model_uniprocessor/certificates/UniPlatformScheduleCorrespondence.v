(* Re-bound copy of the accepted platform_properties PlatformScheduleCorrespondence.v for the
   uniprocessor artifact; only module names differ. *)
(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: Validation/certificates/behavior_schedule/ScheduleCorrespondence.v
    source-sha256: 064580d21d4973cf3a5b5cb0c0bdad4c6039ad1b25aa523e54ef970318d3e2d3
    imported-artifact-sha256: 88c14ae54c0f58e35177b0b34ee0bf1225dad3de38c66d7cf8e5494cf518bf91 *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedUniprocessor ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence UniPlatformScheduleBaseAdapter
  UniPlatformScheduleFiniteOperations.

(** Compositional correspondence for the four derived declarations in
    [behavior/schedule.v].  The relation is intentionally observational:
    processor-state carriers may differ, while explicit state/core maps and
    field relations record precisely the observations used downstream. *)

Inductive SchSourceTrue : SProp := sch_source_true_intro.
Inductive SchSourceFalse : SProp := .

Definition SchSourceBoolTruth (b : bool) : SProp :=
  match b with true => SchSourceTrue | false => SchSourceFalse end.

Definition sch_source_false_elim (Q : SProp)
    (H : SchSourceFalse) : Q := match H return Q with end.

Definition sch_coq_false_ne_true (H : Logic.eq false true) :
    SchSourceFalse :=
  match H in Logic.eq _ z return
    match z with true => SchSourceFalse | false => SchSourceTrue end
  with Logic.eq_refl => sch_source_true_intro end.

Definition sch_source_truth_to_strict (b : bool) :
    SchSourceBoolTruth b -> StrictlyInhabited (is_true b) :=
  match b return SchSourceBoolTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => fun H => sch_source_false_elim _ H
  end.

Definition sch_prop_to_source_truth (b : bool) :
    is_true b -> SchSourceBoolTruth b :=
  match b return is_true b -> SchSourceBoolTruth b with
  | true => fun _ => sch_source_true_intro
  | false => fun H => sch_source_false_elim _ (sch_coq_false_ne_true H)
  end.

Definition sch_bool_true_elim (bR : bool)
    (bL : ImportedUniprocessor.Bool) :
  SchBoolRel bR bL ->
  Lean.eq bL ImportedUniprocessor.Bool_true -> SchSourceBoolTruth bR.
Proof.
  destruct bR, bL; cbn; intros Hrel Htrue.
  - exact sch_source_true_intro.
  - exact sch_source_true_intro.
  - exact (sch_false_elim _ (sch_false_ne_true Htrue)).
  - exact (sch_false_elim _ (sch_false_ne_true Hrel)).
Defined.

Lemma sch_bool_rel_from_truth (bR : bool)
    (bL : ImportedUniprocessor.Bool) :
  (is_true bR -> Lean.eq bL ImportedUniprocessor.Bool_true) ->
  (Lean.eq bL ImportedUniprocessor.Bool_true ->
    StrictlyInhabited (is_true bR)) ->
  SchBoolRel bR bL.
Proof.
  destruct bR, bL; cbn; intros Hforward Hbackward.
  - exact (sch_false_elim _ (sch_false_ne_true
      (Hforward (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - destruct (Hbackward (@Lean.eq_refl _ _)) as [Hfalse].
    exact (sch_source_false_elim _ (sch_coq_false_ne_true Hfalse)).
Qed.

Definition sch_bool_rel_target_transport (bR : bool)
    (x y : ImportedUniprocessor.Bool) :
  SchBoolRel bR x -> Lean.eq x y -> SchBoolRel bR y :=
  fun Hxy Htarget => sub_imported_eq_trans _ _ _ Hxy Htarget.

Definition sch_nat_rel_target_transport (nR : nat)
    (x y : Lean.Nat) :
  SubNatRel nR x -> Lean.eq x y -> SubNatRel nR y :=
  fun Hxy Htarget => sub_imported_eq_trans _ _ _ Hxy Htarget.

Definition sch_exists_intro_strict (T : finType) (p : pred T) (x : T) :
    SchSourceBoolTruth (p x) ->
    StrictlyInhabited (is_true [exists y : T, p y]).
Proof.
  destruct (p x) eqn:Hpx.
  - intro Htruth. apply strictly_inhabits. apply/existsP. exists x.
    exact Hpx.
  - exact (sch_source_false_elim _).
Defined.

Lemma sch_mathcomp_exists_as_has_enum (T : finType) (p : pred T) :
  [exists x : T, p x] = has p (enum T).
Proof.
  apply/idP/idP.
  - move/existsP=> [x Hx]. apply/hasP. exists x; first exact: mem_enum.
    exact Hx.
  - move/hasP=> [x Hmem Hx]. apply/existsP. by exists x.
Qed.

Fixpoint sch_exists_forward_seq
    (CoreR CoreL : Type) (toL : CoreR -> CoreL)
    (pR : CoreR -> bool) (pL : CoreL -> ImportedUniprocessor.Bool)
    (Hpred : forall cR, SchBoolRel (pR cR) (pL (toL cR)))
    (xs : seq CoreR) :
  SchSourceBoolTruth (has pR xs) ->
  ImportedUniprocessor.Exists CoreL
    (fun cL => Lean.eq (pL cL) ImportedUniprocessor.Bool_true) :=
  match xs as ys return
    SchSourceBoolTruth (has pR ys) ->
    ImportedUniprocessor.Exists CoreL
      (fun cL => Lean.eq (pL cL) ImportedUniprocessor.Bool_true)
  with
  | [::] => sch_source_false_elim _
  | cR :: tail =>
      match pR cR as b return
        SchBoolRel b (pL (toL cR)) ->
        SchSourceBoolTruth (b || has pR tail) ->
        ImportedUniprocessor.Exists CoreL
          (fun cL => Lean.eq (pL cL) ImportedUniprocessor.Bool_true)
      with
      | true => fun Hrel _ =>
          ImportedUniprocessor.Exists_intro _ _ (toL cR)
            (sub_imported_eq_sym _ _ Hrel)
      | false => fun _ Htail =>
          sch_exists_forward_seq CoreR CoreL toL pR pL Hpred tail Htail
      end (Hpred cR)
  end.

Section ProcessorStateObservations.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let CoreR : finType := @prosa.behavior.schedule.Core Job PStateR.
  Let StateL : Type :=
    ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState_State Job
      (sch_decidable_eq Job) PStateL.
  Let CoreL : Type :=
    ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState_Core Job
      (sch_decidable_eq Job) PStateL.

  Variable StateRel : StateR -> StateL -> SProp.
  Variables (stateToL : StateR -> StateL) (stateToR : StateL -> StateR).
  Variables (coreToL : CoreR -> CoreL) (coreToR : CoreL -> CoreR).

  Hypothesis state_rel_canonical :
    forall sR, StateRel sR (stateToL sR).
  Hypothesis state_rel_surjective :
    forall sL, StateRel (stateToR sL) sL.
  Hypothesis core_target_roundtrip :
    forall cL, Lean.eq (coreToL (coreToR cL)) cL.

  Definition sch_target_scheduled_on (j : Job) (s : StateL)
      (c : CoreL) : ImportedUniprocessor.Bool :=
    ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState_scheduled_on
      Job (sch_decidable_eq Job) PStateL j s c.

  Definition sch_target_supply_on (s : StateL) (c : CoreL) : Lean.Nat :=
    ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState_supply_on
      Job (sch_decidable_eq Job) PStateL s c.

  Definition sch_target_service_on (j : Job) (s : StateL)
      (c : CoreL) : Lean.Nat :=
    ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState_service_on
      Job (sch_decidable_eq Job) PStateL j s c.

  Hypothesis scheduled_on_rel :
    forall (j : Job) (sR : StateR) (sL : StateL) (cR : CoreR),
      StateRel sR sL ->
      SchBoolRel (@prosa.behavior.schedule.scheduled_on Job PStateR
          j sR cR)
        (sch_target_scheduled_on j sL (coreToL cR)).

  Hypothesis supply_on_rel :
    forall (sR : StateR) (sL : StateL) (cR : CoreR),
      StateRel sR sL ->
      SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
        (sch_target_supply_on sL (coreToL cR)).

  Hypothesis service_on_rel :
    forall (j : Job) (sR : StateR) (sL : StateL) (cR : CoreR),
      StateRel sR sL ->
      SubNatRel (@prosa.behavior.schedule.service_on Job PStateR
          j sR cR)
        (sch_target_service_on j sL (coreToL cR)).

  Hypothesis core_enumeration_rel :
    SchCoreEnumerationRel CoreR CoreL coreToL
      (ImportedUniprocessor.Prosa_Validation_ScheduleInterface_coreEnumeration
        Job (sch_decidable_eq Job) PStateL).

  Lemma scheduled_on_rel_at_target_core (j : Job)
      (sR : StateR) (sL : StateL) (cL : CoreL) :
    StateRel sR sL ->
    SchBoolRel (@prosa.behavior.schedule.scheduled_on Job PStateR
        j sR (coreToR cL))
      (sch_target_scheduled_on j sL cL).
  Proof.
    intro Hstate. apply (sch_bool_rel_target_transport _
      (sch_target_scheduled_on j sL (coreToL (coreToR cL))) _).
    - exact (scheduled_on_rel j sR sL (coreToR cL) Hstate).
    - exact (sub_imported_eq_congr
        (sch_target_scheduled_on j sL) _ _
        (core_target_roundtrip cL)).
  Qed.

  Lemma scheduled_in_correspondence (j : Job)
      (sR : StateR) (sL : StateL) :
    StateRel sR sL ->
    SchBoolRel (@prosa.behavior.schedule.scheduled_in Job PStateR j sR)
      (ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
        Job (sch_decidable_eq Job) PStateL j sL).
  Proof.
    intro Hstate. apply sch_bool_rel_from_truth.
    - intro Hsource.
      have Htruth := sch_prop_to_source_truth _ Hsource.
      unfold prosa.behavior.schedule.scheduled_in in Htruth.
      rewrite sch_mathcomp_exists_as_has_enum in Htruth.
      apply (ImportedUniprocessor.Iff_mpr _ _
        (ImportedUniprocessor.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (sch_decidable_eq Job) PStateL j sL)).
      exact (sch_exists_forward_seq CoreR CoreL coreToL
        [eta @prosa.behavior.schedule.scheduled_on Job PStateR j sR]
        (sch_target_scheduled_on j sL)
        (fun cR => scheduled_on_rel j sR sL cR Hstate)
        (enum CoreR) Htruth).
    - intro Htarget.
      have Hexists := ImportedUniprocessor.Iff_mp _ _
        (ImportedUniprocessor.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (sch_decidable_eq Job) PStateL j sL) Htarget.
      destruct Hexists as [cL Hscheduled].
      apply (sch_exists_intro_strict CoreR
        [eta @prosa.behavior.schedule.scheduled_on Job PStateR j sR]
        (coreToR cL)).
      exact (sch_bool_true_elim _ _
        (scheduled_on_rel_at_target_core j sR sL cL Hstate) Hscheduled).
  Qed.

  Lemma supply_in_correspondence (sR : StateR) (sL : StateL) :
    StateRel sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_in Job PStateR sR)
      (ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState_supply_in
        Job (sch_decidable_eq Job) PStateL sL).
  Proof.
    intro Hstate.
    have Hsum := sch_finite_sum_related CoreR CoreL coreToL
      (fun cR => @prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (sch_target_supply_on sL)
      (ImportedUniprocessor.Prosa_Validation_ScheduleInterface_coreEnumeration
        Job (sch_decidable_eq Job) PStateL)
      (fun cR => supply_on_rel sR sL cR Hstate) core_enumeration_rel.
    unfold SubNatRel in Hsum |- *.
    exact (sub_imported_eq_trans _ _ _ Hsum
      (sub_imported_eq_sym _ _
        (ImportedUniprocessor.Prosa_Validation_ScheduleInterface_production_supply_in_as_list_sum
          Job (sch_decidable_eq Job) PStateL sL))).
  Qed.

  Lemma service_in_correspondence (j : Job)
      (sR : StateR) (sL : StateL) :
    StateRel sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_in Job PStateR j sR)
      (ImportedUniprocessor.Prosa_Behavior_Schedule_ProcessorState_service_in
        Job (sch_decidable_eq Job) PStateL j sL).
  Proof.
    intro Hstate.
    have Hsum := sch_finite_sum_related CoreR CoreL coreToL
      (fun cR => @prosa.behavior.schedule.service_on Job PStateR j sR cR)
      (sch_target_service_on j sL)
      (ImportedUniprocessor.Prosa_Validation_ScheduleInterface_coreEnumeration
        Job (sch_decidable_eq Job) PStateL)
      (fun cR => service_on_rel j sR sL cR Hstate)
      core_enumeration_rel.
    unfold SubNatRel in Hsum |- *.
    exact (sub_imported_eq_trans _ _ _ Hsum
      (sub_imported_eq_sym _ _
        (ImportedUniprocessor.Prosa_Validation_ScheduleInterface_production_service_in_as_list_sum
          Job (sch_decidable_eq Job) PStateL j sL))).
  Qed.

  Definition SchScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedUniprocessor.Prosa_Behavior_Schedule_schedule Job
        (sch_decidable_eq Job) PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL -> StateRel (schedR tR) (schedL tL).

  Definition import_schedule
      (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      ImportedUniprocessor.Prosa_Behavior_Schedule_schedule Job
        (sch_decidable_eq Job) PStateL :=
    fun tL => stateToL (schedR (sub_nat_to_rocq tL)).

  Definition export_schedule
      (schedL : ImportedUniprocessor.Prosa_Behavior_Schedule_schedule Job
        (sch_decidable_eq Job) PStateL) :
      @prosa.behavior.schedule.schedule Job PStateR :=
    fun tR => stateToR (schedL (sub_nat_to_imported tR)).

  Lemma schedule_import_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
    SchScheduleRel schedR (import_schedule schedR).
  Proof.
    intros tR tL Ht. unfold import_schedule.
    have Hdecoded := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Ht).
    rewrite (sub_nat_rocq_roundtrip tR) in Hdecoded.
    rewrite <- Hdecoded. exact (state_rel_canonical _).
  Qed.

  Lemma schedule_export_correspondence
      (schedL : ImportedUniprocessor.Prosa_Behavior_Schedule_schedule Job
        (sch_decidable_eq Job) PStateL) :
    SchScheduleRel (export_schedule schedL) schedL.
  Proof.
    intros tR tL Ht. unfold export_schedule.
    have Htarget := sub_imported_eq_congr schedL _ _ Ht.
    have Hstate := state_rel_surjective (schedL tL).
    have Hcoq := imported_eq_to_coq_eq _ _ Htarget.
    rewrite Hcoq. exact Hstate.
  Qed.

End ProcessorStateObservations.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN scheduled_in_correspondence". exact I. Qed.
Print Assumptions scheduled_in_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END scheduled_in_correspondence". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN supply_in_correspondence". exact I. Qed.
Print Assumptions supply_in_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END supply_in_correspondence". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN service_in_correspondence". exact I. Qed.
Print Assumptions service_in_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END service_in_correspondence". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN schedule_import_correspondence". exact I. Qed.
Print Assumptions schedule_import_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END schedule_import_correspondence". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN schedule_export_correspondence". exact I. Qed.
Print Assumptions schedule_export_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END schedule_export_correspondence". exact I. Qed.
