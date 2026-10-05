# `scheduled_jobs_at_iff`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.scheduled.scheduled_jobs_at_iff`
- Lean: `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_iff`
- Certificate: `scheduled_jobs_at_iff_correspondence`

## Official Rocq

```coq
scheduled_jobs_at_iff :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
forall (j : Equality.sort Job) (t : instant),
(j \in @scheduled_jobs_at Job PState arr_seq sched t) = @scheduled_at Job PState sched j t

scheduled_jobs_at_iff is not universe polymorphic
Arguments scheduled_jobs_at_iff {Job H PState} arr_seq H_valid_arrivals sched
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute j t
scheduled_jobs_at_iff is opaque
Expands to: Constant prosa.analysis.facts.model.scheduled.scheduled_jobs_at_iff
Declared in library prosa.analysis.facts.model.scheduled, line 41, characters 8-29
@scheduled_jobs_at_iff
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall (j : Equality.sort Job) (t : instant),
       (j \in @scheduled_jobs_at Job PState arr_seq sched t) = @scheduled_at Job PState sched j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_iff : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
            decide (j ∈ Prosa.Model.Schedule.Scheduled.scheduled_jobs_at arr_seq sched t) =
              Prosa.Behavior.Service.scheduled_at sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Scheduled_scheduled_jobs_at_iff
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
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
                  inst_3 PState arr_seq
                  sched t)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
                  inst_3 PState arr_seq
                  sched t)))
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
```
