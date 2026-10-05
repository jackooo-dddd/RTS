# `has_arrived_scheduled`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.completion.has_arrived_scheduled`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.has_arrived_scheduled`
- Certificate: `has_arrived_scheduled_correspondence`

## Official Rocq

```coq
has_arrived_scheduled :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) {H0 : JobArrival Job},
@jobs_must_arrive_to_execute Job H0 PState sched ->
forall t : instant, is_true (@scheduled_at Job PState sched j t) -> is_true (@has_arrived Job H0 j t)

has_arrived_scheduled is not universe polymorphic
Arguments has_arrived_scheduled {Job PState} sched j {H0} H_jobs_must_arrive t _
has_arrived_scheduled is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.has_arrived_scheduled
Declared in library prosa.analysis.facts.behavior.completion, line 272, characters 14-35
@has_arrived_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (H0 : JobArrival Job),
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       forall t : instant, is_true (@scheduled_at Job PState sched j t) -> is_true (@has_arrived Job H0 j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.has_arrived_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Arrival_sequence.has_arrived j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_has_arrived_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job)
         (inst_11 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_11 PState sched ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_has_arrived Job
            inst_3
            inst_11 j t)
         Bool_true
```
