From mathcomp Require Import ssreflect ssrbool eqtype.
From prosa Require Import model.readiness.jitter.

Section JitterHelperSourceGuard.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Context `{JobArrival Job} `{JobCost Job} `{JobJitter Job}.

  Definition ji_source_ready : JobReady Job PState :=
    @prosa.model.readiness.jitter.jitter_ready_instance
      Job PState H H0 H1.

  Lemma ji_source_ready_field_guard (sched : schedule PState)
      (j : Job) (t : instant) :
    @prosa.behavior.ready.job_ready Job PState H0 H ji_source_ready
      sched j t =
    is_released j t && ~~ completed_by sched j t.
  Proof. reflexivity. Qed.

End JitterHelperSourceGuard.

Print Assumptions ji_source_ready_field_guard.
