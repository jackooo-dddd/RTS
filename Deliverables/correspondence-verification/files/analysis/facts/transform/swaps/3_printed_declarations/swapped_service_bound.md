# `swapped_service_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.swapped_service_bound`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swapped_service_bound`
- Certificate: `swapped_service_bound_correspondence`

## Official Rocq

```coq
swapped_service_bound :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (t1 t2 : instant),
is_true (t1 <= t2) ->
(forall (j : Equality.sort Job) (t : instant), is_true (@service Job PState sched j t <= @job_cost Job H j)) ->
forall (j : Equality.sort Job) (t : instant),
is_true (@service Job PState (@swapped Job PState sched t1 t2) j t <= @job_cost Job H j)

swapped_service_bound is not universe polymorphic
Arguments swapped_service_bound {Job H PState} sched t1 t2 H_order _%function_scope j t
swapped_service_bound is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swapped_service_bound
Declared in library prosa.analysis.facts.transform.swaps, line 291, characters 8-29
@swapped_service_bound
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (t1 t2 : instant),
       is_true (t1 <= t2) ->
       (forall (j : Equality.sort Job) (t : instant),
        is_true (@service Job PState sched j t <= @job_cost Job H j)) ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@service Job PState (@swapped Job PState sched t1 t2) j t <= @job_cost Job H j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swapped_service_bound : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  [inst_1 : Prosa.Behavior.Job.JobCost Job] (sched : Prosa.Behavior.Schedule.schedule PState)
  (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    (∀ (j : Job) (t : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Service.service sched j t ≤ Prosa.Behavior.Job.job_cost j) →
      ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Service.service (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t ≤
          Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swapped_service_bound
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_8 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       (forall (j : Job) (t : Prosa_Behavior_Time_instant),
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Service_service Job
             inst_3 PState sched j t)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             inst_8 j)) ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Service_service Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            j t)
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_8 j)
```
