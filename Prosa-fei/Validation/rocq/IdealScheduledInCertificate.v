From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype.
From prosa Require Import model.processor.ideal.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ProcessorStateBridge EqTypeBridge.

(** The representation relation between Rocq's standard [option] and the
    monomorphic imported Lean [Option_inst1].  Jobs share the eqType carrier;
    equality behavior is related separately by [EqTypeBridge]. *)
Inductive IdealStateRel (Job : eqType) :
    option Job -> Option_inst1 Job -> SProp :=
| ideal_state_none :
    IdealStateRel Job None (Option_none_inst1 Job)
| ideal_state_some (j : Job) :
    IdealStateRel Job (Some j) (Option_some_inst1 Job j).

Definition ideal_state_to_imported {Job : eqType} (s : option Job) :
    Option_inst1 Job :=
  match s with
  | None => Option_none_inst1 Job
  | Some j => Option_some_inst1 Job j
  end.

Lemma ideal_state_to_imported_rel (Job : eqType) (s : option Job) :
  IdealStateRel Job s (ideal_state_to_imported s).
Proof. by destruct s; constructor. Qed.

Definition imported_option_none_ne_some {A : Type} (x : A)
    (H : eq (Option_none_inst1 A) (Option_some_inst1 A x)) :
    Validation_SFalse :=
  match H in eq _ o return
    match o with
    | Option_none_inst1 => Validation_STrue
    | Option_some_inst1 _ => Validation_SFalse
    end
  with
  | eq_refl => Validation_sI
  end.

Section IdealScheduledIn.
  Context (Job : eqType).

  Let PStateR : prosa.behavior.schedule.ProcessorState Job :=
    prosa.model.processor.ideal.processor_state Job.
  Let StateL : Type := Prosa_Model_Processor_Ideal_processor_state Job.
  Let psL : Prosa_Behavior_Schedule_ProcessorState_inst1 Job StateL :=
    Prosa_Model_Processor_Ideal_pstate_instance
      Job (imported_classical_decidable_eq Job).

  Let CoreR : finType := @prosa.behavior.schedule.Core Job PStateR.
  Let CoreL : Type :=
    Prosa_Behavior_Schedule_ProcessorState_Core_inst1 Job StateL psL.

  Definition ideal_core_toL (_ : CoreR) : CoreL := Unit_unit.
  Definition ideal_core_toR (_ : CoreL) : CoreR := tt.

  Lemma ideal_core_surjective (cL : CoreL) :
    Logic.eq (ideal_core_toL (ideal_core_toR cL)) cL.
  Proof. by destruct cL. Qed.

  Local Transparent
    prosa.behavior.schedule.scheduled_on
    prosa.model.processor.ideal.processor_state.

  Lemma ideal_scheduled_on_rel
      (jR jL : Job) (sR : PStateR) (sL : StateL) (cR : CoreR) :
    eq jR jL ->
    IdealStateRel Job sR sL ->
    ImportedBoolRel
      (prosa.behavior.schedule.scheduled_on jR sR cR)
      (Prosa_Behavior_Schedule_ProcessorState_scheduled_on_inst1
         Job StateL psL jL sL (ideal_core_toL cR)).
  Proof.
    intros Hjob Hstate.
    destruct Hjob.
    destruct Hstate; destruct cR.
    - cbv [PStateR StateL psL CoreR CoreL
           prosa.behavior.schedule.scheduled_on
           prosa.model.processor.ideal.processor_state
           ideal_core_toL
           Prosa_Behavior_Schedule_ProcessorState_scheduled_on_inst1
           Prosa_Model_Processor_Ideal_pstate_instance
           Prosa_Model_Processor_Ideal_ideal_scheduled_at].
      cbn.
      exact Validation_sI.
    - cbv [PStateR StateL psL CoreR CoreL
           prosa.behavior.schedule.scheduled_on
           prosa.model.processor.ideal.processor_state
           ideal_core_toL
           Prosa_Behavior_Schedule_ProcessorState_scheduled_on_inst1
           Prosa_Model_Processor_Ideal_pstate_instance
           Prosa_Model_Processor_Ideal_ideal_scheduled_at].
      cbn.
      exact (eqtype_option_some_imported_decide Job j jR).
  Qed.

  Theorem ideal_scheduled_in_certificate
      (jR jL : Job) (sR : PStateR) (sL : StateL) :
    eq jR jL ->
    IdealStateRel Job sR sL ->
    ImportedBoolRel
      (@prosa.behavior.schedule.scheduled_in Job PStateR jR sR)
      (Prosa_Validation_ideal_scheduled_in
         Job (imported_classical_decidable_eq Job) jL sL).
  Proof.
    unfold Prosa_Validation_ideal_scheduled_in.
    exact
      (@scheduled_in_actual_artifact_rel_bridge_inst1
         Job PStateR Job StateL
         psL eq (IdealStateRel Job)
         ideal_core_toL ideal_core_toR
         ideal_core_surjective ideal_scheduled_on_rel
         jR jL sR sL).
  Qed.
End IdealScheduledIn.

Print Assumptions ideal_scheduled_in_certificate.
