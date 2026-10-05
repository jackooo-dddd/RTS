# `arrives_in_jobs_come_from_arrival_sequence`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrives_in_jobs_come_from_arrival_sequence`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrives_in_jobs_come_from_arrival_sequence`
- Certificate: `arrives_in_jobs_come_from_arrival_sequence_correspondence`

## Official Rocq

```coq
arrives_in_jobs_come_from_arrival_sequence :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> @arrives_in Job arr_seq j

arrives_in_jobs_come_from_arrival_sequence is not universe polymorphic
Arguments arrives_in_jobs_come_from_arrival_sequence {Job PState} arr_seq sched
  H_jobs_come_from_arrival_sequence j t H_scheduled_at
arrives_in_jobs_come_from_arrival_sequence is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrives_in_jobs_come_from_arrival_sequence
Declared in library prosa.analysis.facts.behavior.arrivals, line 538, characters 8-50
@arrives_in_jobs_come_from_arrival_sequence
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) -> @arrives_in Job arr_seq j
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrives_in_jobs_come_from_arrival_sequence : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrives_in_jobs_come_from_arrival_sequence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j
```
