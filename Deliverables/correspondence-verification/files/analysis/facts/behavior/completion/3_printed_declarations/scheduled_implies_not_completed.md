# `scheduled_implies_not_completed`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.scheduled_implies_not_completed`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_not_completed`
- Certificate: `scheduled_implies_not_completed_correspondence`

## Official Rocq

```coq
scheduled_implies_not_completed :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job),
@completed_jobs_dont_execute Job PState sched H ->
forall t : instant,
is_true (@scheduled_at Job PState sched j t) -> is_true (~~ @completed_by Job PState sched H j t)

scheduled_implies_not_completed is not universe polymorphic
Arguments scheduled_implies_not_completed {Job H PState} sched j H_completed_jobs t _
scheduled_implies_not_completed is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.scheduled_implies_not_completed
Declared in library prosa.analysis.facts.behavior.completion, line 139, characters 8-39
@scheduled_implies_not_completed
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       @completed_jobs_dont_execute Job PState sched H ->
       forall t : instant,
       is_true (@scheduled_at Job PState sched j t) -> is_true (~~ @completed_by Job PState sched H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_not_completed : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    ∀ (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j t = true → (!Prosa.Behavior.Service.completed_by sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_scheduled_implies_not_completed
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
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j t))
         Bool_true
```
