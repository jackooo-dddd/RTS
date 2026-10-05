# `arrived_between_jobs_must_arrive_to_execute`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrived_between_jobs_must_arrive_to_execute`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_jobs_must_arrive_to_execute`
- Certificate: `arrived_between_jobs_must_arrive_to_execute_correspondence`

## Official Rocq

```coq
arrived_between_jobs_must_arrive_to_execute :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job H PState sched ->
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> is_true (@has_arrived Job H j t)

arrived_between_jobs_must_arrive_to_execute is not universe polymorphic
Arguments arrived_between_jobs_must_arrive_to_execute {Job H PState} sched H_jobs_must_arrive_to_execute 
  j t H_scheduled_at
arrived_between_jobs_must_arrive_to_execute is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrived_between_jobs_must_arrive_to_execute
Declared in library prosa.analysis.facts.behavior.arrivals, line 545, characters 8-51
@arrived_between_jobs_must_arrive_to_execute
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) -> is_true (@has_arrived Job H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_jobs_must_arrive_to_execute : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Arrival_sequence.has_arrived j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrived_between_jobs_must_arrive_to_execute
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_has_arrived Job
            inst_3
            inst_6 j t)
         Bool_true
```
