# `cumulative_i_ohep_eq_service_of_ohep`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.cumulative_i_ohep_eq_service_of_ohep`
- Lean: `Prosa.Analysis.Facts.Interference.cumulative_i_ohep_eq_service_of_ohep`
- Certificate: `cumulative_i_ohep_eq_service_of_ohep_correspondence`

## Official Rocq

```coq
cumulative_i_ohep_eq_service_of_ohep :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched H2 ->
forall {JLFP : JLFP_policy Job},
@unit_service_proc_model Job PState ->
forall (j : Equality.sort Job) (t1 t : instant),
@quiet_time Job H1 H2 PState arr_seq sched JLFP j t1 ->
@cumulative_another_hep_job_interference Job PState arr_seq sched JLFP j t1 t =
@service_of_other_hep_jobs Job PState arr_seq sched JLFP j t1 t

cumulative_i_ohep_eq_service_of_ohep is not universe polymorphic
Arguments cumulative_i_ohep_eq_service_of_ohep {Job H1 H2 PState} H_uniprocessor_proc_model 
  arr_seq H_valid_arrival_sequence sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  {JLFP} H_unit_service j t1 t H_quiet_time
cumulative_i_ohep_eq_service_of_ohep is opaque
Expands to: Constant prosa.analysis.facts.interference.cumulative_i_ohep_eq_service_of_ohep
Declared in library prosa.analysis.facts.interference, line 416, characters 11-47
@cumulative_i_ohep_eq_service_of_ohep
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched H2 ->
       forall JLFP : JLFP_policy Job,
       @unit_service_proc_model Job PState ->
       forall (j : Equality.sort Job) (t1 t : instant),
       @quiet_time Job H1 H2 PState arr_seq sched JLFP j t1 ->
       @cumulative_another_hep_job_interference Job PState arr_seq sched JLFP j t1 t =
       @service_of_other_hep_jobs Job PState arr_seq sched JLFP j t1 t
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.cumulative_i_ohep_eq_service_of_ohep : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
            Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
              ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
                Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                  ∀ (j : Job) (t1 t : Prosa.Behavior.Time.instant),
                    Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t1 →
                      Prosa.Analysis.Definitions.Interference.cumulative_another_hep_job_interference arr_seq sched j t1
                          t =
                        Prosa.Model.Aggregate.ServiceOfJobs.service_of_other_hep_jobs arr_seq sched j t1 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_cumulative_i_ohep_eq_service_of_ohep
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
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
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_9 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall (j : Job) (t1 t : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched JLFP j t1 ->
       @eq Nat
         (Prosa_Analysis_Definitions_Interference_cumulative_another_hep_job_interference Job
            inst_3 PState arr_seq sched JLFP j
            t1 t)
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_other_hep_jobs Job
            inst_3 PState arr_seq sched JLFP j
            t1 t)
```
