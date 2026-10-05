# `swap_job_scheduled_t2`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.swap_job_scheduled_t2`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_t2`
- Certificate: `swap_job_scheduled_t2_correspondence`

## Official Rocq

```coq
swap_job_scheduled_t2 :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t1 t2 : instant) (j : Equality.sort Job),
@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t2 = @scheduled_at Job PState sched j t1

swap_job_scheduled_t2 is not universe polymorphic
Arguments swap_job_scheduled_t2 {Job PState} sched t1 t2 j
swap_job_scheduled_t2 is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swap_job_scheduled_t2
Declared in library prosa.analysis.facts.transform.swaps, line 76, characters 8-29
@swap_job_scheduled_t2
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t1 t2 : instant) (j : Equality.sort Job),
       @scheduled_at Job PState (@swapped Job PState sched t1 t2) j t2 = @scheduled_at Job PState sched j t1
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_t2 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
  Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t2 =
    Prosa.Behavior.Service.scheduled_at sched j t1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_t2
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
            j t2)
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t1)
```
