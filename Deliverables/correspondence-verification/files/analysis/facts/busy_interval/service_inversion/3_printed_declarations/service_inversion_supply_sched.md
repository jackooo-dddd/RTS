# `service_inversion_supply_sched`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.service_inversion_supply_sched`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_supply_sched`
- Certificate: `service_inversion_supply_sched_correspondence`

## Official Rocq

```coq
service_inversion_supply_sched :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
forall {JLDP : JLDP_policy Job},
@reflexive_priorities Job JLDP ->
forall t : instant,
is_true (@has_supply Job PState sched t) ->
forall j j' : Equality.sort Job,
is_true (@scheduled_at Job PState sched j t) ->
@service_inversion Job PState arr_seq sched JLDP j' t = ~~ @hep_job_at Job JLDP t j j'

service_inversion_supply_sched is not universe polymorphic
Arguments service_inversion_supply_sched {Job H PState} H_uniprocessor_proc_model
  H_consumed_supply_proc_model arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute {JLDP} H_priority_is_reflexive t H_supply j j' H_sched
service_inversion_supply_sched is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.service_inversion.service_inversion_supply_sched
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 135, characters 10-40
@service_inversion_supply_sched
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall JLDP : JLDP_policy Job,
       @reflexive_priorities Job JLDP ->
       forall t : instant,
       is_true (@has_supply Job PState sched t) ->
       forall j j' : Equality.sort Job,
       is_true (@scheduled_at Job PState sched j t) ->
       @service_inversion Job PState arr_seq sched JLDP j' t = ~~ @hep_job_at Job JLDP t j j'
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_supply_sched : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                ∀ (JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job),
                  Prosa.Model.Priority.Definitions.reflexive_priorities JLDP →
                    ∀ (t : Prosa.Behavior.Time.instant),
                      Prosa.Model.Processor.Supply.has_supply sched t = true →
                        ∀ (j j' : Job),
                          Prosa.Behavior.Service.scheduled_at sched j t = true →
                            Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion arr_seq sched j' t =
                              !Prosa.Model.Priority.Definitions.hep_job_at t j j'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inversion_supply_sched
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_3 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
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
         JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_priorities Job
         inst_3 JLDP ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Model_Processor_Supply_has_supply Job
            inst_3 PState
            sched t)
         Bool_true ->
       forall j j' : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState
            sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion Job
            inst_3 PState
            arr_seq sched JLDP j' t)
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
               inst_3 JLDP t
               j j'))
```
