# `scheduled_implies_pending`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.scheduled_implies_pending`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_pending`
- Certificate: `scheduled_implies_pending_correspondence`

## Official Rocq

```coq
scheduled_implies_pending :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState),
@completed_jobs_dont_execute Job PState sched H ->
forall (j : Equality.sort Job) {H0 : JobArrival Job},
@jobs_must_arrive_to_execute Job H0 PState sched ->
forall t : instant,
is_true (@scheduled_at Job PState sched j t) -> is_true (@pending Job PState sched H H0 j t)

scheduled_implies_pending is not universe polymorphic
Arguments scheduled_implies_pending {Job H PState} sched H_completed_jobs j {H0} H_jobs_must_arrive t _
scheduled_implies_pending is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.scheduled_implies_pending
Declared in library prosa.analysis.facts.behavior.completion, line 278, characters 10-35
@scheduled_implies_pending
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState),
       @completed_jobs_dont_execute Job PState sched H ->
       forall (j : Equality.sort Job) (H0 : JobArrival Job),
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       forall t : instant,
       is_true (@scheduled_at Job PState sched j t) -> is_true (@pending Job PState sched H H0 j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_pending : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    ∀ (j : Job) [inst_2 : Prosa.Behavior.Job.JobArrival Job],
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
        ∀ (t : Prosa.Behavior.Time.instant),
          Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Service.pending sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_scheduled_implies_pending
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_6 ->
       forall (j : Job)
         (inst_19 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_19 PState sched ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched
            inst_6
            inst_19 j t)
         Bool_true
```
