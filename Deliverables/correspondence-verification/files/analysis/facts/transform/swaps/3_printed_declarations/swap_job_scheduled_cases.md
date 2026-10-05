# `swap_job_scheduled_cases`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.transform.swaps.swap_job_scheduled_cases`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_cases`
- Certificate: `swap_job_scheduled_cases_correspondence`

## Official Rocq

```coq
swap_job_scheduled_cases :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t1 t2 : instant) (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t) ->
@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t = @scheduled_at Job PState sched j t \/
t = t1 /\
@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t = @scheduled_at Job PState sched j t2 \/
t = t2 /\
@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t = @scheduled_at Job PState sched j t1

swap_job_scheduled_cases is not universe polymorphic
Arguments swap_job_scheduled_cases {Job PState} sched t1 t2 j t _
swap_job_scheduled_cases is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swap_job_scheduled_cases
Declared in library prosa.analysis.facts.transform.swaps, line 102, characters 12-36
@swap_job_scheduled_cases
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t1 t2 : instant) (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t) ->
       @scheduled_at Job PState (@swapped Job PState sched t1 t2) j t = @scheduled_at Job PState sched j t \/
       t = t1 /\
       @scheduled_at Job PState (@swapped Job PState sched t1 t2) j t = @scheduled_at Job PState sched j t2 \/
       t = t2 /\
       @scheduled_at Job PState (@swapped Job PState sched t1 t2) j t = @scheduled_at Job PState sched j t1
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_cases : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t = true →
    Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t =
        Prosa.Behavior.Service.scheduled_at sched j t ∨
      t = t1 ∧
          Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t =
            Prosa.Behavior.Service.scheduled_at sched j t2 ∨
        t = t2 ∧
          Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t =
            Prosa.Behavior.Service.scheduled_at sched j t1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_cases
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
       Or
         (@eq Bool
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState
               (Prosa_Analysis_Transform_Swap_swapped Job
                  inst_3 PState sched t1 t2)
               j t)
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j t))
         (Or
            (And (@eq Prosa_Behavior_Time_instant t t1)
               (@eq Bool
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState
                     (Prosa_Analysis_Transform_Swap_swapped Job
                        inst_3 PState sched
                        t1 t2)
                     j t)
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState sched j
                     t2)))
            (And (@eq Prosa_Behavior_Time_instant t t2)
               (@eq Bool
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState
                     (Prosa_Analysis_Transform_Swap_swapped Job
                        inst_3 PState sched
                        t1 t2)
                     j t)
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState sched j
                     t1))))
```
