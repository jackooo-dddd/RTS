From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype.
From prosa Require Import behavior.schedule.
Require Import Relations FiniteBridge.

Section ScheduledInObservableBridge.
  Context {Job : JobType} {PState : ProcessorState Job}.

  Variables (CoreL : finType).
  Variables (toL : Core -> CoreL) (toR : CoreL -> Core).
  Hypothesis toR_toL : cancel toL toR.
  Hypothesis toL_toR : cancel toR toL.
  Variable scheduled_onL : Job -> PState -> CoreL -> bool.
  Hypothesis scheduled_on_rel :
    forall j s cR, scheduled_on j s cR = scheduled_onL j s (toL cR).

  Definition scheduled_inL_model (j : Job) (s : PState) : bool :=
    [exists cL : CoreL, scheduled_onL j s cL].

  Lemma scheduled_in_observable_bridge j s :
    BoolRel (scheduled_in j s) (scheduled_inL_model j s).
  Proof.
    rewrite /BoolRel /scheduled_in /scheduled_inL_model.
    exact: finite_exists_bridge.
  Qed.
End ScheduledInObservableBridge.
