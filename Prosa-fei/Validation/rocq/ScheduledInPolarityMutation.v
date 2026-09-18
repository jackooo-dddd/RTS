From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype.
From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ProcessorStateBridge.

(** Negative test fixture only.  This deliberately changes the polarity of
    the result returned by the actual imported Lean [scheduled_in].  The
    production Lean source and the exported artifact are not modified. *)
Definition imported_bool_not (b : Bool) : Bool :=
  match b with
  | Bool_false => Bool_true
  | Bool_true => Bool_false
  end.

Section PolarityMutationMustBeRejected.
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

  Definition scheduled_in_polarity_mutation (j : Job) (s : PState) : Bool :=
    imported_bool_not
      (Prosa_Behavior_Schedule_ProcessorState_scheduled_in
         Job PState psL j s).

  (** The actual-artifact certificate must not type-check after the translated
      result is replaced by the polarity mutation.  [Fail Definition] makes
      rejection itself part of this Rocq-checked fixture: the file fails if
      Rocq ever accepts the invalid certificate. *)
  Fail Definition scheduled_in_polarity_mutation_certificate (j : Job)
      (s : PState) :
      ImportedBoolRel
        (prosa.behavior.schedule.scheduled_in j s)
        (scheduled_in_polarity_mutation j s) :=
    scheduled_in_actual_artifact_bridge
      psL toL toR core_surjective scheduled_on_rel j s.
End PolarityMutationMustBeRejected.
