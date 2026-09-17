From mathcomp Require Import ssreflect ssrbool ssrnat.
From prosa Require Import behavior.service.
Require Import Relations NatBridge.

(** Conditional bridge scaffolding. [serviceL] and [costL] are placeholders
    for the not-yet-imported Lean declarations, so this theorem is not a
    semantic certificate for the repository's Lean artifact. *)
Section CompletedByBridge.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  Variables (serviceL : Job -> nat -> nat) (costL : Job -> nat).
  Hypothesis service_rel : forall j t, NatRel (service sched j t) (serviceL j t).
  Hypothesis cost_rel : forall j, NatRel (job_cost j) (costL j).

  Definition completed_byL_model (j : Job) (t : nat) : Prop :=
    (costL j <= serviceL j t)%coq_nat.

  Lemma completed_by_compositional_bridge j t :
    BoolPropRel (completed_by sched j t) (completed_byL_model j t).
  Proof.
    rewrite /completed_by /completed_byL_model.
    exact: nat_ge_bool_prop_bridge (service_rel j t) (cost_rel j).
  Qed.
End CompletedByBridge.
