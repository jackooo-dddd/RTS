# `scheduled_jobs_at_nil`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.scheduled.scheduled_jobs_at_nil`
- Lean: `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_nil`
- Certificate: `scheduled_jobs_at_nil_correspondence`

## Official Rocq

```coq
scheduled_jobs_at_nil :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
forall t : instant,
is_true (@nilp (Equality.sort Job) (@scheduled_jobs_at Job PState arr_seq sched t)) <->
(forall j : Equality.sort Job, is_true (~~ @scheduled_at Job PState sched j t))

scheduled_jobs_at_nil is not universe polymorphic
Arguments scheduled_jobs_at_nil {Job H PState} arr_seq H_valid_arrivals sched
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute t
scheduled_jobs_at_nil is opaque
Expands to: Constant prosa.analysis.facts.model.scheduled.scheduled_jobs_at_nil
Declared in library prosa.analysis.facts.model.scheduled, line 50, characters 8-29
@scheduled_jobs_at_nil
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall t : instant,
       is_true (@nilp (Equality.sort Job) (@scheduled_jobs_at Job PState arr_seq sched t)) <->
       (forall j : Equality.sort Job, is_true (~~ @scheduled_at Job PState sched j t))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_nil : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (t : Prosa.Behavior.Time.instant),
            (Prosa.Model.Schedule.Scheduled.scheduled_jobs_at arr_seq sched t).isEmpty = true ↔
              ∀ (j : Job), (!Prosa.Behavior.Service.scheduled_at sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Scheduled_scheduled_jobs_at_nil
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall t : Prosa_Behavior_Time_instant,
       Iff
         (@eq Bool
            (List_isEmpty Job
               (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
                  inst_3 PState arr_seq
                  sched t))
            Bool_true)
         (forall j : Job,
          @eq Bool
            (Bool_not
               (Prosa_Behavior_Service_scheduled_at Job
                  inst_3 PState sched j t))
            Bool_true)
```
