# `priority_inversion_hep_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.inversion.priority_inversion_hep_job`
- Lean: `Prosa.Analysis.Facts.Priority.Inversion.priority_inversion_hep_job`
- Certificate: `priority_inversion_hep_job_correspondence`

## Official Rocq

```coq
priority_inversion_hep_job :
forall {Job : JobType} {H1 : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall j : Equality.sort Job,
@uniprocessor_model Job PState ->
forall (t : instant) (j' : Equality.sort Job),
is_true (@scheduled_at Job PState sched j' t) ->
@priority_inversion Job PState arr_seq sched JLFP j t = ~~ @hep_job Job JLFP j' j

priority_inversion_hep_job is not universe polymorphic
Arguments priority_inversion_hep_job {Job H1 PState} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP} H_priority_is_reflexive 
  j H_uni t j' _
priority_inversion_hep_job is opaque
Expands to: Constant prosa.analysis.facts.priority.inversion.priority_inversion_hep_job
Declared in library prosa.analysis.facts.priority.inversion, line 87, characters 10-36
@priority_inversion_hep_job
     : forall (Job : JobType) (H1 : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall j : Equality.sort Job,
       @uniprocessor_model Job PState ->
       forall (t : instant) (j' : Equality.sort Job),
       is_true (@scheduled_at Job PState sched j' t) ->
       @priority_inversion Job PState arr_seq sched JLFP j t = ~~ @hep_job Job JLFP j' j
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Inversion.priority_inversion_hep_job : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
            Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
              ∀ (j : Job),
                Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
                  ∀ (t : Prosa.Behavior.Time.instant) (j' : Job),
                    Prosa.Behavior.Service.scheduled_at sched j' t = true →
                      Prosa.Analysis.Definitions.PriorityInversion.priority_inversion arr_seq sched j t =
                        !Prosa.Model.Priority.Definitions.hep_job j' j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Inversion_priority_inversion_hep_job
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
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall j : Job,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall (t : Prosa_Behavior_Time_instant) (j' : Job),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j' t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion Job
            inst_3 PState arr_seq sched
            JLFP j t)
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
               inst_3 JLFP j' j))
```
