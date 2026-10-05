# `idle_implies_no_service_inversion`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.idle_implies_no_service_inversion`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.idle_implies_no_service_inversion`
- Certificate: `idle_implies_no_service_inversion_correspondence`

## Official Rocq

```coq
idle_implies_no_service_inversion :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
forall {JLDP : JLDP_policy Job} (j : Equality.sort Job) (t : instant),
is_true (@is_idle Job PState arr_seq sched t) ->
is_true (~~ @service_inversion Job PState arr_seq sched JLDP j t)

idle_implies_no_service_inversion is not universe polymorphic
Arguments idle_implies_no_service_inversion {Job H PState} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLDP} j 
  t _
idle_implies_no_service_inversion is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.service_inversion.idle_implies_no_service_inversion
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 56, characters 10-43
@idle_implies_no_service_inversion
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall (JLDP : JLDP_policy Job) (j : Equality.sort Job) (t : instant),
       is_true (@is_idle Job PState arr_seq sched t) ->
       is_true (~~ @service_inversion Job PState arr_seq sched JLDP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.idle_implies_no_service_inversion : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job) (j : Job) (t : Prosa.Behavior.Time.instant),
            Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
              (!Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_idle_implies_no_service_inversion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
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
                   inst_3
                   PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched
         arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall
         (JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
                   inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState
            arr_seq sched t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion Job
               inst_3 PState
               arr_seq sched JLDP j t))
         Bool_true
```
