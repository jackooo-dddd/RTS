# `interference_ahep_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.interference_ahep_def`
- Lean: `Prosa.Analysis.Facts.Interference.interference_ahep_def`
- Certificate: `interference_ahep_def_correspondence`

## Official Rocq

```coq
interference_ahep_def :
forall {Job : JobType} {H1 : JobArrival Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job} (j : Equality.sort Job) (t : instant),
is_true (@has_supply Job PState sched t) ->
forall j' : Equality.sort Job,
is_true (@scheduled_at Job PState sched j' t) ->
@another_hep_job_interference Job PState arr_seq sched JLFP j t = @another_hep_job Job JLFP j' j

interference_ahep_def is not universe polymorphic
Arguments interference_ahep_def {Job H1 PState} H_uniprocessor_proc_model H_consumed_supply_proc_model
  arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  {JLFP} j t H_supply j' H_sched
interference_ahep_def is opaque
Expands to: Constant prosa.analysis.facts.interference.interference_ahep_def
Declared in library prosa.analysis.facts.interference, line 234, characters 12-33
@interference_ahep_def
     : forall (Job : JobType) (H1 : JobArrival Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (JLFP : JLFP_policy Job) (j : Equality.sort Job) (t : instant),
       is_true (@has_supply Job PState sched t) ->
       forall j' : Equality.sort Job,
       is_true (@scheduled_at Job PState sched j' t) ->
       @another_hep_job_interference Job PState arr_seq sched JLFP j t = @another_hep_job Job JLFP j' j
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.interference_ahep_def : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job) (t : Prosa.Behavior.Time.instant),
                  Prosa.Model.Processor.Supply.has_supply sched t = true →
                    ∀ (j' : Job),
                      Prosa.Behavior.Service.scheduled_at sched j' t = true →
                        Prosa.Analysis.Definitions.Interference.another_hep_job_interference arr_seq sched j t =
                          Prosa.Model.Priority.Definitions.another_hep_job j' j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_interference_ahep_def
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
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
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Supply_has_supply Job
            inst_3 PState sched t)
         Bool_true ->
       forall j' : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j' t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_Interference_another_hep_job_interference Job
            inst_3 PState arr_seq sched JLFP
            j t)
         (Prosa_Model_Priority_Definitions_another_hep_job Job
            inst_3 JLFP j' j)
```
