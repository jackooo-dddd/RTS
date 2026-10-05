# `scheduled_at_implies_later_deadline`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.deadlines.scheduled_at_implies_later_deadline`
- Lean: `Prosa.Analysis.Facts.Behavior.Deadlines.scheduled_at_implies_later_deadline`
- Certificate: `scheduled_at_implies_later_deadline_correspondence`

## Official Rocq

```coq
scheduled_at_implies_later_deadline :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState),
@completed_jobs_dont_execute Job PState sched H ->
forall (j : Equality.sort Job) (t : instant),
is_true (@job_meets_deadline Job PState sched H H0 j) ->
is_true (@scheduled_at Job PState sched j t) -> is_true (t < @job_deadline Job H0 j)

scheduled_at_implies_later_deadline is not universe polymorphic
Arguments scheduled_at_implies_later_deadline {Job H H0 PState} sched H_completed_jobs j t _ _
scheduled_at_implies_later_deadline is opaque
Expands to: Constant prosa.analysis.facts.behavior.deadlines.scheduled_at_implies_later_deadline
Declared in library prosa.analysis.facts.behavior.deadlines, line 68, characters 10-45
@scheduled_at_implies_later_deadline
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState),
       @completed_jobs_dont_execute Job PState sched H ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@job_meets_deadline Job PState sched H H0 j) ->
       is_true (@scheduled_at Job PState sched j t) -> is_true (t < @job_deadline Job H0 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Deadlines.scheduled_at_implies_later_deadline : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.job_meets_deadline sched j = true →
        Prosa.Behavior.Service.scheduled_at sched j t = true → t < Prosa.Behavior.Job.job_deadline j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Deadlines_scheduled_at_implies_later_deadline
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_6 ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline Job
            inst_3 PState sched
            inst_6
            inst_9 j)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j)
```
