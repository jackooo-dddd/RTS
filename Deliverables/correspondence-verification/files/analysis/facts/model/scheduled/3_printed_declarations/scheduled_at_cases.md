# `scheduled_at_cases`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.scheduled.scheduled_at_cases`
- Lean: `Prosa.Analysis.Facts.Model.Scheduled.scheduled_at_cases`
- Certificate: `scheduled_at_cases_correspondence`

## Official Rocq

```coq
scheduled_at_cases :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
forall t : instant,
is_true (@is_idle Job PState arr_seq sched t) \/
(exists j : Equality.sort Job, is_true (@scheduled_at Job PState sched j t))

scheduled_at_cases is not universe polymorphic
Arguments scheduled_at_cases {Job H PState} arr_seq H_valid_arrivals sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute t
scheduled_at_cases is opaque
Expands to: Constant prosa.analysis.facts.model.scheduled.scheduled_at_cases
Declared in library prosa.analysis.facts.model.scheduled, line 221, characters 12-30
@scheduled_at_cases
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall t : instant,
       is_true (@is_idle Job PState arr_seq sched t) \/
       (exists j : Equality.sort Job, is_true (@scheduled_at Job PState sched j t))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Scheduled.scheduled_at_cases : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (t : Prosa.Behavior.Time.instant),
            Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true ∨
              ∃ j, Prosa.Behavior.Service.scheduled_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Scheduled_scheduled_at_cases
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
       Or
         (@eq Bool
            (Prosa_Model_Schedule_Scheduled_is_idle Job
               inst_3 PState arr_seq sched
               t)
            Bool_true)
         (Exists Job
            (fun j : Job =>
             Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j t =
             Bool_true))
```
