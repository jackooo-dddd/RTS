# `swap_job_scheduled_original`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.transform.swaps.swap_job_scheduled_original`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_original`
- Certificate: `swap_job_scheduled_original_correspondence`

## Official Rocq

```coq
swap_job_scheduled_original :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t1 t2 : instant) (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) ->
exists t' : instant, is_true (@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t')

swap_job_scheduled_original is not universe polymorphic
Arguments swap_job_scheduled_original {Job PState} sched t1 t2 j t _
swap_job_scheduled_original is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swap_job_scheduled_original
Declared in library prosa.analysis.facts.transform.swaps, line 166, characters 12-39
@swap_job_scheduled_original
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t1 t2 : instant) (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) ->
       exists t' : instant, is_true (@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_original : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.scheduled_at sched j t = true →
    ∃ t', Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_original
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant) (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       Exists Prosa_Behavior_Time_instant
         (fun t' : Prosa_Behavior_Time_instant =>
          Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            j t' =
          Bool_true)
```
