From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype.
From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
Require Import ImportedEasy93.
Require Import Relations FiniteBridge.

(** A relation between the Rocq/MathComp [bool] and the [Bool] type imported
    from the actual Lean artifact.  It deliberately lives in [SProp], matching
    the importer's representation of Lean propositions. *)
Inductive Validation_STrue : SProp := Validation_sI.
Inductive Validation_SFalse : SProp := .

Definition Validation_false_elim (P : SProp)
    (H : Validation_SFalse) : P :=
  match H return P with end.

Definition ImportedBoolRel (bR : bool) (bL : Bool) : SProp :=
  match bR, bL with
  | true, Bool_true => Validation_STrue
  | false, Bool_false => Validation_STrue
  | _, _ => Validation_SFalse
  end.

Definition RocqBoolTruth (b : bool) : SProp :=
  match b with
  | true => Validation_STrue
  | false => Validation_SFalse
  end.

Lemma mathcomp_exists_as_has_enum (T : finType) (p : pred T) :
  [exists x : T, p x] = has p (enum T).
Proof.
  apply/idP/idP.
  - move/existsP=> [x Hx].
    apply/hasP. exists x; first exact: mem_enum.
    exact Hx.
  - move/hasP=> [x Hmem Hx].
    apply/existsP. by exists x.
Qed.

Definition coq_bool_false_ne_true
    (H : Logic.eq false true) : Validation_SFalse :=
  match H in Logic.eq _ b return
    match b with
    | false => Validation_STrue
    | true => Validation_SFalse
    end
  with
  | Logic.eq_refl => Validation_sI
  end.

Definition bool_imp_truth (a b : bool) :
    is_true (a ==> b) -> RocqBoolTruth a -> RocqBoolTruth b :=
  match a, b return
    is_true (a ==> b) -> RocqBoolTruth a -> RocqBoolTruth b
  with
  | true, true => fun Himp Ha => Validation_sI
  | true, false => fun Himp Ha => coq_bool_false_ne_true Himp
  | false, true => fun Himp Ha => Validation_sI
  | false, false => fun Himp Ha => Ha
  end.

Lemma mathcomp_exists_imp (T : finType) (p : pred T) (x : T) :
  p x ==> [exists y : T, p y].
Proof.
  apply/implyP=> Hx.
  exact (existsb x Hx).
Qed.

Definition mathcomp_exists_intro_truth
    (T : finType) (p : pred T) (x : T) :
    RocqBoolTruth (p x) -> RocqBoolTruth [exists y : T, p y] :=
  bool_imp_truth _ _ (mathcomp_exists_imp T p x).

Lemma imported_bool_true_intro bL :
  ImportedBoolRel true bL -> eq bL Bool_true.
Proof.
  destruct bL; cbn.
  - intro H. destruct H.
  - intro H. exact (eq_refl Bool_true).
Qed.

Definition imported_bool_false_ne_true
    (H : eq Bool_false Bool_true) : Validation_SFalse :=
  match H in eq _ b return
    match b with
    | Bool_false => Validation_STrue
    | Bool_true => Validation_SFalse
    end
  with
  | eq_refl => Validation_sI
  end.

Lemma imported_bool_true_elim bR bL :
  ImportedBoolRel bR bL -> eq bL Bool_true -> RocqBoolTruth bR.
Proof.
  destruct bR; destruct bL; cbn.
  - intros Hrel Heq. destruct Hrel.
  - intros Hrel Heq. exact Hrel.
  - intros Hrel Heq. exact (imported_bool_false_ne_true Heq).
  - intros Hrel Heq. exact Hrel.
Qed.

Lemma imported_decide_bridge (bR : bool) (p : SProp) (d : Decidable p) :
  (RocqBoolTruth bR -> p) ->
  (p -> RocqBoolTruth bR) ->
  ImportedBoolRel bR (Decidable_decide p d).
Proof.
  intros Hforward Hbackward.
  destruct bR; destruct d as [Hfalse | Htrue]; cbn in *.
  - destruct (Hfalse (Hforward Validation_sI)).
  - exact Validation_sI.
  - exact Validation_sI.
  - exact (Hbackward Htrue).
Qed.

Section ImportedFiniteExistsForward.
  Variables (CoreR CoreL : Type).
  Variable toL : CoreR -> CoreL.
  Variables (pR : CoreR -> bool) (pL : CoreL -> Bool).
  Hypothesis predicate_rel :
    forall cR, ImportedBoolRel (pR cR) (pL (toL cR)).

  Fixpoint imported_exists_forward_seq (xs : seq CoreR) :
    RocqBoolTruth (has pR xs) ->
    Exists CoreL (fun cL => eq (pL cL) Bool_true) :=
    match xs as xs0 return
      RocqBoolTruth (has pR xs0) ->
      Exists CoreL (fun cL => eq (pL cL) Bool_true)
    with
    | [::] => Validation_false_elim _
    | cR :: xs' =>
        match pR cR as b return
          ImportedBoolRel b (pL (toL cR)) ->
          RocqBoolTruth (b || has pR xs') ->
          Exists CoreL (fun cL => eq (pL cL) Bool_true)
        with
        | true => fun Hrel H =>
            Exists_intro _ _ (toL cR)
              (imported_bool_true_intro _ Hrel)
        | false => fun Hrel H => imported_exists_forward_seq xs' H
        end (predicate_rel cR)
    end.
End ImportedFiniteExistsForward.

Section ScheduledInActualArtifactBridge.
  Context {Job : prosa.behavior.job.JobType}.
  Context {PState : prosa.behavior.schedule.ProcessorState Job}.

  Let CoreR : finType := @prosa.behavior.schedule.Core Job PState.

  Variable psL : Prosa_Behavior_Schedule_ProcessorState Job PState.

  Let CoreL : Type :=
    Prosa_Behavior_Schedule_ProcessorState_Core Job PState psL.
  Let scheduled_onL : Job -> PState -> CoreL -> Bool :=
    Prosa_Behavior_Schedule_ProcessorState_scheduled_on Job PState psL.

  Variables (toL : CoreR -> CoreL) (toR : CoreL -> CoreR).
  Hypothesis core_surjective : forall cL, Logic.eq (toL (toR cL)) cL.
  Hypothesis scheduled_on_rel :
    forall j s cR,
      ImportedBoolRel
        (prosa.behavior.schedule.scheduled_on j s cR)
        (scheduled_onL j s (toL cR)).

  Lemma scheduled_in_actual_artifact_bridge j s :
    ImportedBoolRel
      (prosa.behavior.schedule.scheduled_in j s)
      (Prosa_Behavior_Schedule_ProcessorState_scheduled_in
         Job PState psL j s).
  Proof.
    unfold Prosa_Behavior_Schedule_ProcessorState_scheduled_in.
    apply imported_decide_bridge.
    - intro HR.
      rewrite /prosa.behavior.schedule.scheduled_in in HR.
      rewrite mathcomp_exists_as_has_enum in HR.
      exact
        (imported_exists_forward_seq
           CoreR CoreL toL
           [eta prosa.behavior.schedule.scheduled_on j s]
           (fun cL => scheduled_onL j s cL)
           (scheduled_on_rel j s)
           (enum CoreR) HR).
    - intro HL.
      destruct HL as [cL HscheduledL].
      have Hrel := scheduled_on_rel j s (toR cL).
      have Hsurj := core_surjective cL.
      rewrite Hsurj in Hrel.
      apply
        (mathcomp_exists_intro_truth
           CoreR [eta prosa.behavior.schedule.scheduled_on j s] (toR cL)).
      exact (imported_bool_true_elim _ _ Hrel HscheduledL).
  Qed.
End ScheduledInActualArtifactBridge.

(** Cross-carrier form of the same certificate.  Unlike the compatibility
    theorem above, this permits the original and imported translations to use
    different job and processor-state representations.  Only the observable
    relations needed by [scheduled_in] occur in the interface. *)
Section ScheduledInActualArtifactRelBridge.
  Context {JobR : prosa.behavior.job.JobType}.
  Context {PStateR : prosa.behavior.schedule.ProcessorState JobR}.
  Context {JobL StateL : Type}.

  Let CoreR : finType := @prosa.behavior.schedule.Core JobR PStateR.

  Variable psL : Prosa_Behavior_Schedule_ProcessorState JobL StateL.

  Let CoreL : Type :=
    Prosa_Behavior_Schedule_ProcessorState_Core JobL StateL psL.
  Let scheduled_onL : JobL -> StateL -> CoreL -> Bool :=
    Prosa_Behavior_Schedule_ProcessorState_scheduled_on JobL StateL psL.

  Variables (JobRel : JobR -> JobL -> SProp).
  Variables (StateRel : PStateR -> StateL -> SProp).
  Variables (toL : CoreR -> CoreL) (toR : CoreL -> CoreR).

  Hypothesis core_surjective : forall cL, Logic.eq (toL (toR cL)) cL.
  Hypothesis scheduled_on_rel :
    forall jR jL sR sL cR,
      JobRel jR jL ->
      StateRel sR sL ->
      ImportedBoolRel
        (prosa.behavior.schedule.scheduled_on jR sR cR)
        (scheduled_onL jL sL (toL cR)).

  Lemma scheduled_in_actual_artifact_rel_bridge jR jL sR sL :
    JobRel jR jL ->
    StateRel sR sL ->
    ImportedBoolRel
      (prosa.behavior.schedule.scheduled_in jR sR)
      (Prosa_Behavior_Schedule_ProcessorState_scheduled_in
         JobL StateL psL jL sL).
  Proof.
    intros Hjob Hstate.
    unfold Prosa_Behavior_Schedule_ProcessorState_scheduled_in.
    apply imported_decide_bridge.
    - intro HR.
      rewrite /prosa.behavior.schedule.scheduled_in in HR.
      rewrite mathcomp_exists_as_has_enum in HR.
      exact
        (imported_exists_forward_seq
           CoreR CoreL toL
           [eta prosa.behavior.schedule.scheduled_on jR sR]
           (fun cL => scheduled_onL jL sL cL)
           (fun cR => scheduled_on_rel jR jL sR sL cR Hjob Hstate)
           (enum CoreR) HR).
    - intro HL.
      destruct HL as [cL HscheduledL].
      have Hrel := scheduled_on_rel jR jL sR sL (toR cL) Hjob Hstate.
      have Hsurj := core_surjective cL.
      rewrite Hsurj in Hrel.
      apply
        (mathcomp_exists_intro_truth
           CoreR [eta prosa.behavior.schedule.scheduled_on jR sR] (toR cL)).
      exact (imported_bool_true_elim _ _ Hrel HscheduledL).
  Qed.
End ScheduledInActualArtifactRelBridge.

(** The legacy exporter specializes small-universe applications into the
    importer's [_inst1] record family.  This theorem is the same reusable
    semantic interface for that actual imported universe specialization. *)
Section ScheduledInActualArtifactRelBridgeInst1.
  Context {JobR : prosa.behavior.job.JobType}.
  Context {PStateR : prosa.behavior.schedule.ProcessorState JobR}.
  Context {JobL StateL : Type}.

  Let CoreR : finType := @prosa.behavior.schedule.Core JobR PStateR.

  Variable psL : Prosa_Behavior_Schedule_ProcessorState_inst1 JobL StateL.

  Let CoreL : Type :=
    Prosa_Behavior_Schedule_ProcessorState_Core_inst1 JobL StateL psL.
  Let scheduled_onL : JobL -> StateL -> CoreL -> Bool :=
    Prosa_Behavior_Schedule_ProcessorState_scheduled_on_inst1 JobL StateL psL.

  Variables (JobRel : JobR -> JobL -> SProp).
  Variables (StateRel : PStateR -> StateL -> SProp).
  Variables (toL : CoreR -> CoreL) (toR : CoreL -> CoreR).

  Hypothesis core_surjective : forall cL, Logic.eq (toL (toR cL)) cL.
  Hypothesis scheduled_on_rel :
    forall jR jL sR sL cR,
      JobRel jR jL ->
      StateRel sR sL ->
      ImportedBoolRel
        (prosa.behavior.schedule.scheduled_on jR sR cR)
        (scheduled_onL jL sL (toL cR)).

  Lemma scheduled_in_actual_artifact_rel_bridge_inst1 jR jL sR sL :
    JobRel jR jL ->
    StateRel sR sL ->
    ImportedBoolRel
      (prosa.behavior.schedule.scheduled_in jR sR)
      (Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst1
         JobL StateL psL jL sL).
  Proof.
    intros Hjob Hstate.
    unfold Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst1.
    apply imported_decide_bridge.
    - intro HR.
      rewrite /prosa.behavior.schedule.scheduled_in in HR.
      rewrite mathcomp_exists_as_has_enum in HR.
      exact
        (imported_exists_forward_seq
           CoreR CoreL toL
           [eta prosa.behavior.schedule.scheduled_on jR sR]
           (fun cL => scheduled_onL jL sL cL)
           (fun cR => scheduled_on_rel jR jL sR sL cR Hjob Hstate)
           (enum CoreR) HR).
    - intro HL.
      destruct HL as [cL HscheduledL].
      have Hrel := scheduled_on_rel jR jL sR sL (toR cL) Hjob Hstate.
      have Hsurj := core_surjective cL.
      rewrite Hsurj in Hrel.
      apply
        (mathcomp_exists_intro_truth
           CoreR [eta prosa.behavior.schedule.scheduled_on jR sR] (toR cL)).
      exact (imported_bool_true_elim _ _ Hrel HscheduledL).
  Qed.
End ScheduledInActualArtifactRelBridgeInst1.
