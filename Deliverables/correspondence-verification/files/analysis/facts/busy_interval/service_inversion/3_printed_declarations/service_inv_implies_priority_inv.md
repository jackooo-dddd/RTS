# `service_inv_implies_priority_inv`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.service_inv_implies_priority_inv`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inv_implies_priority_inv`
- Certificate: `service_inv_implies_priority_inv_correspondence`

## Official Rocq

```coq
service_inv_implies_priority_inv :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall (j : Equality.sort Job) (t : instant),
is_true (@service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t) ->
is_true (@priority_inversion Job PState arr_seq sched JLFP j t)

service_inv_implies_priority_inv is not universe polymorphic
Arguments service_inv_implies_priority_inv {Job H PState} H_uniprocessor_proc_model 
  arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  {JLFP} H_priority_is_reflexive j t _
service_inv_implies_priority_inv is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.service_inversion.service_inv_implies_priority_inv
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 167, characters 10-42
@service_inv_implies_priority_inv
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t) ->
       is_true (@priority_inversion Job PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inv_implies_priority_inv : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
            Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
              ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
                Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
                    Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion arr_seq sched j t = true →
                      Prosa.Analysis.Definitions.PriorityInversion.priority_inversion arr_seq sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inv_implies_priority_inv
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
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion Job
            inst_3 PState
            arr_seq sched
            (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
               inst_3 JLFP)
            j t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion Job
            inst_3 PState
            arr_seq sched JLFP j t)
         Bool_true
```
