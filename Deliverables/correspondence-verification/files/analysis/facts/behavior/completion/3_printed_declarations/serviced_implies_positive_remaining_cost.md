# `serviced_implies_positive_remaining_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.serviced_implies_positive_remaining_cost`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.serviced_implies_positive_remaining_cost`
- Certificate: `serviced_implies_positive_remaining_cost_correspondence`

## Official Rocq

```coq
serviced_implies_positive_remaining_cost :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job),
@completed_jobs_dont_execute Job PState sched H ->
forall t : instant,
is_true (0 < @service_at Job PState sched j t) -> is_true (0 < @remaining_cost Job PState sched H j t)

serviced_implies_positive_remaining_cost is not universe polymorphic
Arguments serviced_implies_positive_remaining_cost {Job H PState} sched j H_completed_jobs t _
serviced_implies_positive_remaining_cost is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.serviced_implies_positive_remaining_cost
Declared in library prosa.analysis.facts.behavior.completion, line 103, characters 8-48
@serviced_implies_positive_remaining_cost
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       @completed_jobs_dont_execute Job PState sched H ->
       forall t : instant,
       is_true (0 < @service_at Job PState sched j t) -> is_true (0 < @remaining_cost Job PState sched H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.serviced_implies_positive_remaining_cost : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    ∀ (t : Prosa.Behavior.Time.instant),
      0 < Prosa.Behavior.Service.service_at sched j t → 0 < Prosa.Behavior.Service.remaining_cost sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_serviced_implies_positive_remaining_cost
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
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t) ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_remaining_cost Job
            inst_3 PState sched
            inst_6 j t)
```
