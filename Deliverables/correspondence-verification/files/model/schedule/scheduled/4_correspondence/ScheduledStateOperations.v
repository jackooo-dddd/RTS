(** Artifact-local replay of accepted EdfOperations.v (SHA-256
    907023b1f3a52e832a74f89bb493f1d8b0e66d642ea39546d434a97f328c6444).
    Only the imported module, base-adapter module, and source import name were
    substituted. The complete proof body is rechecked by Rocq here. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.schedule.scheduled.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduledFull.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ScheduledStateBaseAdapter.

(** Only the already certified finite scheduled-in truth interface and the
    state/core observations actually consumed by Scheduled are used below. In
    particular, scheduled-at correspondence is proved, not postulated. *)

Inductive EdfSourceTrue : SProp := edf_source_true_intro.
Inductive EdfSourceFalse : SProp := .

Definition EdfSourceBoolTruth (b : bool) : SProp :=
  match b with true => EdfSourceTrue | false => EdfSourceFalse end.

Definition edf_source_false_elim (Q : SProp)
    (H : EdfSourceFalse) : Q := match H return Q with end.

Definition edf_coq_false_ne_true (H : Logic.eq false true) :
    EdfSourceFalse :=
  match H in Logic.eq _ z return
    match z with true => EdfSourceFalse | false => EdfSourceTrue end
  with Logic.eq_refl => edf_source_true_intro end.

Definition edf_prop_to_source_truth (b : bool) :
    is_true b -> EdfSourceBoolTruth b :=
  match b return is_true b -> EdfSourceBoolTruth b with
  | true => fun _ => edf_source_true_intro
  | false => fun H => edf_source_false_elim _
      (edf_coq_false_ne_true H)
  end.

Definition edf_bool_true_elim (bR : bool)
    (bL : ImportedScheduledFull.Bool) :
  EdfBoolRel bR bL ->
  Lean.eq bL ImportedScheduledFull.Bool_true ->
  EdfSourceBoolTruth bR.
Proof.
  destruct bR, bL; cbn; intros Hrel Htrue.
  - exact edf_source_true_intro.
  - exact edf_source_true_intro.
  - exact (edf_false_elim _ (edf_false_ne_true Htrue)).
  - exact (edf_false_elim _ (edf_false_ne_true Hrel)).
Defined.

Definition edf_exists_intro_strict (T : finType) (p : pred T)
    (x : T) :
  EdfSourceBoolTruth (p x) ->
  StrictlyInhabited (is_true [exists y : T, p y]).
Proof.
  destruct (p x) eqn:Hpx.
  - intro Htruth. apply strictly_inhabits. apply/existsP.
    exists x. exact Hpx.
  - exact (edf_source_false_elim _).
Defined.

Lemma edf_mathcomp_exists_as_has_enum (T : finType) (p : pred T) :
  [exists x : T, p x] = has p (enum T).
Proof.
  apply/idP/idP.
  - move/existsP=> [x Hx]. apply/hasP.
    exists x; first exact: mem_enum. exact Hx.
  - move/hasP=> [x _ Hx]. apply/existsP.
    exists x. exact Hx.
Qed.

Fixpoint edf_exists_forward_seq
    (CoreR CoreL : Type) (toL : CoreR -> CoreL)
    (pR : CoreR -> bool) (pL : CoreL -> ImportedScheduledFull.Bool)
    (Hpred : forall cR, EdfBoolRel (pR cR) (pL (toL cR)))
    (xs : seq CoreR) :
  EdfSourceBoolTruth (has pR xs) ->
  ImportedScheduledFull.Exists CoreL
    (fun cL => Lean.eq (pL cL) ImportedScheduledFull.Bool_true) :=
  match xs as ys return
    EdfSourceBoolTruth (has pR ys) ->
    ImportedScheduledFull.Exists CoreL
      (fun cL => Lean.eq (pL cL) ImportedScheduledFull.Bool_true)
  with
  | [::] => edf_source_false_elim _
  | cR :: tail =>
      match pR cR as b return
        EdfBoolRel b (pL (toL cR)) ->
        EdfSourceBoolTruth (b || has pR tail) ->
        ImportedScheduledFull.Exists CoreL
          (fun cL => Lean.eq (pL cL) ImportedScheduledFull.Bool_true)
      with
      | true => fun Hrel _ =>
          ImportedScheduledFull.Exists_intro _ _ (toL cR)
            (sub_imported_eq_sym _ _ Hrel)
      | false => fun _ Htail =>
          edf_exists_forward_seq CoreR CoreL toL pR pL Hpred tail Htail
      end (Hpred cR)
  end.

Section EdfProcessorObservation.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState Job
      (edf_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let CoreR : finType := @prosa.behavior.schedule.Core Job PStateR.
  Let StateL : Type :=
    ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState_State
      Job (edf_decidable_eq Job) PStateL.
  Let CoreL : Type :=
    ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState_Core
      Job (edf_decidable_eq Job) PStateL.

  Definition edf_target_scheduled_on (j : Job) (s : StateL)
      (c : CoreL) : ImportedScheduledFull.Bool :=
    ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState_scheduled_on
      Job (edf_decidable_eq Job) PStateL j s c.

  Record EdfProcessorRel : Type := {
    edf_state_to_target : StateR -> StateL;
    edf_core_to_target : CoreR -> CoreL;
    edf_core_to_source : CoreL -> CoreR;
    edf_core_target_roundtrip : forall cL,
      Lean.eq (edf_core_to_target (edf_core_to_source cL)) cL;
    edf_scheduled_on_related : forall j sR cR,
      EdfBoolRel
        (@prosa.behavior.schedule.scheduled_on Job PStateR j sR cR)
        (edf_target_scheduled_on j (edf_state_to_target sR)
          (edf_core_to_target cR))
  }.

  Variable R : EdfProcessorRel.

  Definition EdfScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedScheduledFull.Prosa_Behavior_Schedule_schedule
        Job (edf_decidable_eq Job) PStateL) : SProp :=
    forall tL : Lean.Nat,
      Lean.eq (edf_state_to_target R (schedR (sub_nat_to_rocq tL)))
        (schedL tL).

  Definition edf_schedule_to_target
      (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      ImportedScheduledFull.Prosa_Behavior_Schedule_schedule
        Job (edf_decidable_eq Job) PStateL :=
    fun tL => edf_state_to_target R (schedR (sub_nat_to_rocq tL)).

  Lemma edf_schedule_canonical schedR :
    EdfScheduleRel schedR (edf_schedule_to_target schedR).
  Proof. intro tL. exact (@Lean.eq_refl _ _). Qed.

  Lemma edf_schedule_at_related schedR schedL (tR : nat)
      (tL : Lean.Nat) :
    EdfScheduleRel schedR schedL ->
    SubNatRel tR tL ->
    Lean.eq (edf_state_to_target R (schedR tR)) (schedL tL).
  Proof.
    intros Hsched Ht. destruct Ht.
    have H := Hsched (sub_nat_to_imported tR).
    rewrite (sub_nat_rocq_roundtrip tR) in H.
    exact H.
  Qed.

  Lemma edf_scheduled_in_truth (j : Job)
      (sR : StateR) (sL : StateL) :
    Lean.eq (edf_state_to_target R sR) sL ->
    PropSPropRel
      (is_true (@prosa.behavior.schedule.scheduled_in
        Job PStateR j sR))
      (Lean.eq
        (ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
          Job (edf_decidable_eq Job) PStateL j sL)
        ImportedScheduledFull.Bool_true).
  Proof.
    intro Hstate. apply prop_sprop_rel_intro.
    - intro Hsource.
      have Htruth := edf_prop_to_source_truth _ Hsource.
      unfold prosa.behavior.schedule.scheduled_in in Htruth.
      rewrite edf_mathcomp_exists_as_has_enum in Htruth.
      apply (ImportedScheduledFull.mpr _ _
        (ImportedScheduledFull.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (edf_decidable_eq Job) PStateL j sL)).
      exact (edf_exists_forward_seq CoreR CoreL
        (edf_core_to_target R)
        (fun c => @prosa.behavior.schedule.scheduled_on
          Job PStateR j sR c)
        (edf_target_scheduled_on j sL)
        (fun cR => sub_imported_eq_trans _ _ _
          (edf_scheduled_on_related R j sR cR)
          (sub_imported_eq_congr
            (fun s => edf_target_scheduled_on j s
              (edf_core_to_target R cR)) _ _ Hstate))
        (enum CoreR) Htruth).
    - intro Htarget.
      have Hexists := ImportedScheduledFull.mp _ _
        (ImportedScheduledFull.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (edf_decidable_eq Job) PStateL j sL) Htarget.
      destruct Hexists as [cL Hcore].
      apply (edf_exists_intro_strict CoreR
        (fun c => @prosa.behavior.schedule.scheduled_on
          Job PStateR j sR c) (edf_core_to_source R cL)).
      have Hrel := edf_scheduled_on_related R j sR
        (edf_core_to_source R cL).
      have Hmapped := sub_imported_eq_congr2
        (edf_target_scheduled_on j)
        (edf_state_to_target R sR) sL
        (edf_core_to_target R (edf_core_to_source R cL)) cL
        Hstate (edf_core_target_roundtrip R cL).
      exact (edf_bool_true_elim _ _
        (sub_imported_eq_trans _ _ _ Hrel Hmapped) Hcore).
  Qed.

  Lemma edf_scheduled_at_truth schedR schedL
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    EdfScheduleRel schedR schedL ->
    SubNatRel tR tL ->
    PropSPropRel
      (is_true (@prosa.behavior.service.scheduled_at
        Job PStateR schedR j tR))
      (Lean.eq
        (ImportedScheduledFull.Prosa_Behavior_Service_scheduled_at
          Job (edf_decidable_eq Job) PStateL schedL j tL)
        ImportedScheduledFull.Bool_true).
  Proof.
    intros Hsched Ht.
    unfold prosa.behavior.service.scheduled_at.
    cbn [ImportedScheduledFull.Prosa_Behavior_Service_scheduled_at].
    exact (edf_scheduled_in_truth j (schedR tR) (schedL tL)
      (edf_schedule_at_related schedR schedL tR tL Hsched Ht)).
  Qed.
End EdfProcessorObservation.
