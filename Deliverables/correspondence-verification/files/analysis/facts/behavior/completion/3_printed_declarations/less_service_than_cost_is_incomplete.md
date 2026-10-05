# `less_service_than_cost_is_incomplete`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.less_service_than_cost_is_incomplete`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.less_service_than_cost_is_incomplete`
- Certificate: `less_service_than_cost_is_incomplete_correspondence`

## Official Rocq

```coq
less_service_than_cost_is_incomplete :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t : instant),
is_true (@service Job PState sched j t < @job_cost Job H j) <->
is_true (~~ @completed_by Job PState sched H j t)

less_service_than_cost_is_incomplete is not universe polymorphic
Arguments less_service_than_cost_is_incomplete {Job H PState} sched j t
less_service_than_cost_is_incomplete is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.less_service_than_cost_is_incomplete
Declared in library prosa.analysis.facts.behavior.completion, line 44, characters 8-44
@less_service_than_cost_is_incomplete
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (@service Job PState sched j t < @job_cost Job H j) <->
       is_true (~~ @completed_by Job PState sched H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.less_service_than_cost_is_incomplete : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.service sched j t < Prosa.Behavior.Job.job_cost j ↔
    (!Prosa.Behavior.Service.completed_by sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_less_service_than_cost_is_incomplete
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       Iff
         (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
            (Prosa_Behavior_Service_service Job
               inst_3 PState sched j t)
            (Prosa_Behavior_Job_JobCost_job_cost Job
               inst_3
               inst_6 j))
         (@eq Bool
            (Bool_not
               (Prosa_Behavior_Service_completed_by Job
                  inst_3 PState sched
                  inst_6 j t))
            Bool_true)
```
