# `swap_job_scheduled`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.transform.swaps.swap_job_scheduled`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled`
- Certificate: `swap_job_scheduled_correspondence`

## Official Rocq

```coq
swap_job_scheduled :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t1 t2 : instant) (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t) ->
exists t' : instant, is_true (@scheduled_at Job PState sched j t')

swap_job_scheduled is not universe polymorphic
Arguments swap_job_scheduled {Job PState} sched t1 t2 j t _
swap_job_scheduled is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swap_job_scheduled
Declared in library prosa.analysis.facts.transform.swaps, line 126, characters 12-30
@swap_job_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t1 t2 : instant) (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t) ->
       exists t' : instant, is_true (@scheduled_at Job PState sched j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  (t1 t2 : Prosa.Behavior.Time.instant) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t = true →
    ∃ t', Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant) (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            j t)
         Bool_true ->
       Exists Prosa_Behavior_Time_instant
         (fun t' : Prosa_Behavior_Time_instant =>
          Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t' =
          Bool_true)
```
