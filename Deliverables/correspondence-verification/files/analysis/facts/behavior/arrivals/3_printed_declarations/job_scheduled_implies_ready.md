# `job_scheduled_implies_ready`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.job_scheduled_implies_ready`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.job_scheduled_implies_ready`
- Certificate: `job_scheduled_implies_ready_correspondence`

## Official Rocq

```coq
job_scheduled_implies_ready :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  {H : JobCost Job} {H0 : JobArrival Job} {jr : @JobReady Job PState H H0},
@jobs_must_be_ready_to_execute Job H0 PState sched H jr ->
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> is_true (@job_ready Job PState H H0 jr sched j t)

job_scheduled_implies_ready is not universe polymorphic
Arguments job_scheduled_implies_ready {Job PState} sched {H H0 jr} _ j t _
job_scheduled_implies_ready is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.job_scheduled_implies_ready
Declared in library prosa.analysis.facts.behavior.arrivals, line 99, characters 8-35
@job_scheduled_implies_ready
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (H : JobCost Job) (H0 : JobArrival Job) (jr : @JobReady Job PState H H0),
       @jobs_must_be_ready_to_execute Job H0 PState sched H jr ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) -> is_true (@job_ready Job PState H H0 jr sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.job_scheduled_implies_ready : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
  Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Ready.job_ready sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_job_scheduled_implies_ready
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_10 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_13 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_16 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_10
            inst_13),
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job
         inst_3
         inst_13 PState sched
         inst_10
         inst_16 ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Ready_JobReady_job_ready Job
            inst_3 PState
            inst_10
            inst_13
            inst_16 sched j t)
         Bool_true
```
