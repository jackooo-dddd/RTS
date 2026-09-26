(** Artifact-local replay of the accepted ScheduledStateOperations.v,
    specialized to the compiled TDMA import and its local Bool/eqType adapter.
    The complete proof body is rechecked by Rocq against this artifact. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.schedule.tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTdmaProjectedFull.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence TdmaBaseAdapter.

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
    (bL : ImportedTdmaProjectedFull.Bool) :
  ArBoolRel bR bL ->
  Lean.eq bL ImportedTdmaProjectedFull.Bool_true ->
  EdfSourceBoolTruth bR.
Proof.
  destruct bR, bL; cbn; intros Hrel Htrue.
  - exact edf_source_true_intro.
  - exact edf_source_true_intro.
  - exact (ar_false_elim _ (ar_false_ne_true Htrue)).
  - exact (ar_false_elim _ (ar_false_ne_true Hrel)).
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
    (pR : CoreR -> bool) (pL : CoreL -> ImportedTdmaProjectedFull.Bool)
    (Hpred : forall cR, ArBoolRel (pR cR) (pL (toL cR)))
    (xs : seq CoreR) :
  EdfSourceBoolTruth (has pR xs) ->
  ImportedTdmaProjectedFull.Exists CoreL
    (fun cL => Lean.eq (pL cL) ImportedTdmaProjectedFull.Bool_true) :=
  match xs as ys return
    EdfSourceBoolTruth (has pR ys) ->
    ImportedTdmaProjectedFull.Exists CoreL
      (fun cL => Lean.eq (pL cL) ImportedTdmaProjectedFull.Bool_true)
  with
  | [::] => edf_source_false_elim _
  | cR :: tail =>
      match pR cR as b return
        ArBoolRel b (pL (toL cR)) ->
        EdfSourceBoolTruth (b || has pR tail) ->
        ImportedTdmaProjectedFull.Exists CoreL
          (fun cL => Lean.eq (pL cL) ImportedTdmaProjectedFull.Bool_true)
      with
      | true => fun Hrel _ =>
          ImportedTdmaProjectedFull.Exists_intro _ _ (toL cR)
            (sub_imported_eq_sym _ _ Hrel)
      | false => fun _ Htail =>
          edf_exists_forward_seq CoreR CoreL toL pR pL Hpred tail Htail
      end (Hpred cR)
  end.

Section EdfProcessorObservation.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_ProcessorState Job
      (ar_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let CoreR : finType := @prosa.behavior.schedule.Core Job PStateR.
  Let StateL : Type :=
    ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_ProcessorState_State
      Job (ar_decidable_eq Job) PStateL.
  Let CoreL : Type :=
    ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_ProcessorState_Core
      Job (ar_decidable_eq Job) PStateL.

  Definition edf_target_scheduled_on (j : Job) (s : StateL)
      (c : CoreL) : ImportedTdmaProjectedFull.Bool :=
    ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_ProcessorState_scheduled_on
      Job (ar_decidable_eq Job) PStateL j s c.

  Record EdfProcessorRel : Type := {
    edf_state_to_target : StateR -> StateL;
    edf_core_to_target : CoreR -> CoreL;
    edf_core_to_source : CoreL -> CoreR;
    edf_core_target_roundtrip : forall cL,
      Lean.eq (edf_core_to_target (edf_core_to_source cL)) cL;
    edf_scheduled_on_related : forall j sR cR,
      ArBoolRel
        (@prosa.behavior.schedule.scheduled_on Job PStateR j sR cR)
        (edf_target_scheduled_on j (edf_state_to_target sR)
          (edf_core_to_target cR))
  }.

  Variable R : EdfProcessorRel.

  Definition EdfScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_schedule
        Job (ar_decidable_eq Job) PStateL) : SProp :=
    forall tL : Lean.Nat,
      Lean.eq (edf_state_to_target R (schedR (sub_nat_to_rocq tL)))
        (schedL tL).

  Definition edf_schedule_to_target
      (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_schedule
        Job (ar_decidable_eq Job) PStateL :=
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
        (ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
          Job (ar_decidable_eq Job) PStateL j sL)
        ImportedTdmaProjectedFull.Bool_true).
  Proof.
    intro Hstate. apply prop_sprop_rel_intro.
    - intro Hsource.
      have Htruth := edf_prop_to_source_truth _ Hsource.
      unfold prosa.behavior.schedule.scheduled_in in Htruth.
      rewrite edf_mathcomp_exists_as_has_enum in Htruth.
      apply (ImportedTdmaProjectedFull.mpr _ _
        (ImportedTdmaProjectedFull.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (ar_decidable_eq Job) PStateL j sL)).
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
      have Hexists := ImportedTdmaProjectedFull.mp _ _
        (ImportedTdmaProjectedFull.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (ar_decidable_eq Job) PStateL j sL) Htarget.
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
        (ImportedTdmaProjectedFull.Prosa_Behavior_Service_scheduled_at
          Job (ar_decidable_eq Job) PStateL schedL j tL)
        ImportedTdmaProjectedFull.Bool_true).
  Proof.
    intros Hsched Ht.
    unfold prosa.behavior.service.scheduled_at.
    cbn [ImportedTdmaProjectedFull.Prosa_Behavior_Service_scheduled_at].
    exact (edf_scheduled_in_truth j (schedR tR) (schedL tL)
      (edf_schedule_at_related schedR schedL tR tL Hsched Ht)).
  Qed.
End EdfProcessorObservation.
