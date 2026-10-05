# `no_service_received_when_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.no_service_received_when_idle`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.no_service_received_when_idle`
- Certificate: `no_service_received_when_idle_correspondence`

## Official Rocq

```coq
no_service_received_when_idle :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
forall (j : Equality.sort Job) (t : instant),
is_true (@is_idle Job PState arr_seq sched t) -> is_true (~~ @receives_service_at Job PState sched j t)

no_service_received_when_idle is not universe polymorphic
Arguments no_service_received_when_idle {Job H PState} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute j t _
no_service_received_when_idle is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.no_service_received_when_idle
Declared in library prosa.analysis.facts.behavior.service, line 689, characters 8-37
@no_service_received_when_idle
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@is_idle Job PState arr_seq sched t) ->
       is_true (~~ @receives_service_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.no_service_received_when_idle : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
            Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
              (!Prosa.Behavior.Service.receives_service_at sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_no_service_received_when_idle
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
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState arr_seq sched t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_receives_service_at Job
               inst_3 PState sched j t))
         Bool_true
```
