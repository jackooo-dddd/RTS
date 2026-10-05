# `scheduled_implies_no_interference`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_instantiation.scheduled_implies_no_interference`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.scheduled_implies_no_interference`
- Certificate: `scheduled_implies_no_interference_correspondence`

## Official Rocq

```coq
scheduled_implies_no_interference :
forall {Job : JobType} {H1 : JobArrival Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall (j : Equality.sort Job) (t : instant),
is_true (@receives_service_at Job PState sched j t) ->
is_true (~~ @interference Job (@rs_jlfp_interference Job PState arr_seq sched JLFP) j t)

scheduled_implies_no_interference is not universe polymorphic
Arguments scheduled_implies_no_interference {Job H1 PState} H_uniprocessor_proc_model
  H_consumed_supply_proc_model arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute {JLFP} H_priority_is_reflexive j t _
scheduled_implies_no_interference is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_instantiation.scheduled_implies_no_interference
Declared in library prosa.analysis.abstract.restricted_supply.iw_instantiation, line 485, characters 12-45
@scheduled_implies_no_interference
     : forall (Job : JobType) (H1 : JobArrival Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@receives_service_at Job PState sched j t) ->
       is_true (~~ @interference Job (@rs_jlfp_interference Job PState arr_seq sched JLFP) j t)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.scheduled_implies_no_interference : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
                  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
                      Prosa.Behavior.Service.receives_service_at sched j t = true →
                        (!Prosa.Analysis.Abstract.Definitions.interference j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_scheduled_implies_no_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10
         arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_10 PState
         sched ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at Job
            inst_7
            PState sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
               inst_7
               (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
                  inst_7
                  PState arr_seq sched JLFP)
               j t))
         Bool_true
```
