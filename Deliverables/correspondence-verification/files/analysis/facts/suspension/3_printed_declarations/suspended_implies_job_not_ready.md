# `suspended_implies_job_not_ready`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.suspension.suspended_implies_job_not_ready`
- Lean: `Prosa.Analysis.Facts.Suspension.suspended_implies_job_not_ready`
- Certificate: `suspended_implies_job_not_ready_correspondence`

## Official Rocq

```coq
suspended_implies_job_not_ready :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobSuspension Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t : instant),
is_true (@suspended Job PState H H0 H1 sched j t) ->
is_true (~~ @job_ready Job PState H0 H (@suspension_ready_instance Job PState H H0 H1) sched j t)

suspended_implies_job_not_ready is not universe polymorphic
Arguments suspended_implies_job_not_ready {Job H H0 H1 PState} sched j t _
suspended_implies_job_not_ready is opaque
Expands to: Constant prosa.analysis.facts.suspension.suspended_implies_job_not_ready
Declared in library prosa.analysis.facts.suspension, line 35, characters 8-39
@suspended_implies_job_not_ready
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobSuspension Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (j : Equality.sort Job) 
         (t : instant),
       is_true (@suspended Job PState H H0 H1 sched j t) ->
       is_true (~~ @job_ready Job PState H0 H (@suspension_ready_instance Job PState H H0 H1) sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Suspension.suspended_implies_job_not_ready : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Readiness.Suspension.JobSuspension Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Readiness.Suspension.suspended sched j t = true → (!Prosa.Behavior.Ready.job_ready sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Suspension_suspended_implies_job_not_ready
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
         (inst_9 : Prosa_Behavior_Job_JobCost
                                                                                Job
                                                                                inst_3)
         (inst_12 : 
          Prosa_Model_Readiness_Suspension_JobSuspension Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Readiness_Suspension_suspended Job
            inst_3 PState
            inst_6
            inst_9
            inst_12 sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Ready_JobReady_job_ready Job
               inst_3 PState
               inst_9
               inst_6
               (Prosa_Model_Readiness_Suspension_suspension_ready_instance Job
                  inst_3 PState
                  inst_6
                  inst_9
                  inst_12)
               sched j t))
         Bool_true
```
