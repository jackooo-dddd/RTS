# `swap_job_scheduled_t1`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.swap_job_scheduled_t1`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_t1`
- Certificate: `swap_job_scheduled_t1_correspondence`

## Official Rocq

```coq
swap_job_scheduled_t1 :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t1 t2 : instant) (j : Equality.sort Job),
@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t1 = @scheduled_at Job PState sched j t2

swap_job_scheduled_t1 is not universe polymorphic
Arguments swap_job_scheduled_t1 {Job PState} sched t1 t2 j
swap_job_scheduled_t1 is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swap_job_scheduled_t1
Declared in library prosa.analysis.facts.transform.swaps, line 63, characters 8-29
@swap_job_scheduled_t1
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t1 t2 : instant) (j : Equality.sort Job),
       @scheduled_at Job PState (@swapped Job PState sched t1 t2) j t1 = @scheduled_at Job PState sched j t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_t1 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
  Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t1 =
    Prosa.Behavior.Service.scheduled_at sched j t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_t1
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant) (j : Job),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            j t1)
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t2)
```
