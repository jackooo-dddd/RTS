# `uni_priority_inversion_P`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.inversion.uni_priority_inversion_P`
- Lean: `Prosa.Analysis.Facts.Priority.Inversion.uni_priority_inversion_P`
- Certificate: `uni_priority_inversion_P_correspondence`

## Official Rocq

```coq
uni_priority_inversion_P :
forall {Job : JobType} {H1 : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall j : Equality.sort Job,
@uniprocessor_model Job PState ->
forall t : instant,
reflect
  (exists2 j' : Equality.sort Job,
     is_true (@scheduled_at Job PState sched j' t) & is_true (~~ @hep_job Job JLFP j' j))
  (@priority_inversion Job PState arr_seq sched JLFP j t)

uni_priority_inversion_P is not universe polymorphic
Arguments uni_priority_inversion_P {Job H1 PState} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP} H_priority_is_reflexive 
  j H_uni t
uni_priority_inversion_P is opaque
Expands to: Constant prosa.analysis.facts.priority.inversion.uni_priority_inversion_P
Declared in library prosa.analysis.facts.priority.inversion, line 121, characters 10-34
@uni_priority_inversion_P
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
       forall t : instant,
       reflect
         (exists2 j' : Equality.sort Job,
            is_true (@scheduled_at Job PState sched j' t) & is_true (~~ @hep_job Job JLFP j' j))
         (@priority_inversion Job PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Inversion.uni_priority_inversion_P : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) →
          Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
            (sched : Prosa.Behavior.Schedule.schedule PState) →
              Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
                Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                  [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                    Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                      (j : Job) →
                        Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
                          (t : Prosa.Behavior.Time.instant) →
                            Prosa.Analysis.Definitions.BusyInterval.Classical.BoolReflect
                              (∃ j',
                                Prosa.Behavior.Service.scheduled_at sched j' t = true ∧
                                  (!Prosa.Model.Priority.Definitions.hep_job j' j) = true)
                              (Prosa.Analysis.Definitions.PriorityInversion.priority_inversion arr_seq sched j t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Inversion_uni_priority_inversion_P
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
       forall t : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect
         (Exists Job
            (fun j' : Job =>
             And
               (@eq Bool
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState
                     sched j' t)
                  Bool_true)
               (@eq Bool
                  (Bool_not
                     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                        inst_3 JLFP j'
                        j))
                  Bool_true)))
         (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion Job
            inst_3 PState arr_seq sched
            JLFP j t)
```
