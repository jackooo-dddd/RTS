# `service_lt_cost`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.completion.service_lt_cost`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.service_lt_cost`
- Certificate: `service_lt_cost_correspondence`

## Official Rocq

```coq
service_lt_cost :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job),
@completed_jobs_dont_execute Job PState sched H ->
forall t : instant,
is_true (@scheduled_at Job PState sched j t) -> is_true (@service Job PState sched j t < @job_cost Job H j)

service_lt_cost is not universe polymorphic
Arguments service_lt_cost {Job H PState} sched j H_completed_jobs t _
service_lt_cost is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.service_lt_cost
Declared in library prosa.analysis.facts.behavior.completion, line 87, characters 12-27
@service_lt_cost
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       @completed_jobs_dont_execute Job PState sched H ->
       forall t : instant,
       is_true (@scheduled_at Job PState sched j t) ->
       is_true (@service Job PState sched j t < @job_cost Job H j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.service_lt_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    ∀ (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j t = true →
        Prosa.Behavior.Service.service sched j t < Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_service_lt_cost
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_6 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t)
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j)
```
