From prosa Require Import model.readiness.basic.

Check (@prosa.model.readiness.basic.basic_ready_instance).
Print prosa.model.readiness.basic.basic_ready_instance.
Print Instances prosa.behavior.ready.JobReady.
Print Assumptions prosa.model.readiness.basic.basic_ready_instance.

Section BasicReadyInterface.
  Context {Job : prosa.behavior.job.JobType}.
  Context {PState : prosa.behavior.schedule.ProcessorState Job}.
  Context {arrival : prosa.behavior.job.JobArrival Job}.
  Context {cost : prosa.behavior.job.JobCost Job}.

  Lemma basic_ready_instance_job_ready
      (sched : prosa.behavior.schedule.schedule PState)
      (j : Job) (t : prosa.behavior.time.instant) :
    @prosa.behavior.ready.job_ready Job PState cost arrival
      (@prosa.model.readiness.basic.basic_ready_instance
        Job PState arrival cost) sched j t =
    @prosa.behavior.service.pending Job PState sched cost arrival j t.
  Proof. by []. Qed.

  Lemma basic_ready_instance_law
      (sched : prosa.behavior.schedule.schedule PState)
      (j : Job) (t : prosa.behavior.time.instant) :
    @prosa.behavior.ready.job_ready Job PState cost arrival
      (@prosa.model.readiness.basic.basic_ready_instance
        Job PState arrival cost) sched j t ->
    @prosa.behavior.service.pending Job PState sched cost arrival j t.
  Proof. by []. Qed.
End BasicReadyInterface.

Print Assumptions basic_ready_instance_job_ready.
Print Assumptions basic_ready_instance_law.
