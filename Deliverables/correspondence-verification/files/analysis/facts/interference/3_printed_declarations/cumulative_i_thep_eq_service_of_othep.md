# `cumulative_i_thep_eq_service_of_othep`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.cumulative_i_thep_eq_service_of_othep`
- Lean: `Prosa.Analysis.Facts.Interference.cumulative_i_thep_eq_service_of_othep`
- Certificate: `cumulative_i_thep_eq_service_of_othep_correspondence`

## Official Rocq

```coq
cumulative_i_thep_eq_service_of_othep :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} {PState : ProcessorState Job},
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
@cumulative_another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t1 t =
@service_of_other_task_hep_jobs Task Job H0 PState arr_seq sched JLFP j t1 t

cumulative_i_thep_eq_service_of_othep is not universe polymorphic
Arguments cumulative_i_thep_eq_service_of_othep {Task Job H0 H1 H2 PState} H_uniprocessor_proc_model 
  arr_seq H_valid_arrival_sequence sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  {JLFP} H_unit_service j t1 t H_quiet_time
cumulative_i_thep_eq_service_of_othep is opaque
Expands to: Constant prosa.analysis.facts.interference.cumulative_i_thep_eq_service_of_othep
Declared in library prosa.analysis.facts.interference, line 426, characters 10-47
@cumulative_i_thep_eq_service_of_othep
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (PState : ProcessorState Job),
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
       @cumulative_another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t1 t =
       @service_of_other_task_hep_jobs Task Job H0 PState arr_seq sched JLFP j t1 t
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.cumulative_i_thep_eq_service_of_othep : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
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
                      Prosa.Analysis.Definitions.Interference.cumulative_another_task_hep_job_interference arr_seq sched
                          j t1 t =
                        Prosa.Model.Aggregate.ServiceOfJobs.service_of_other_task_hep_jobs arr_seq sched j t1 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_cumulative_i_thep_eq_service_of_othep
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7 PState,
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_14 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7 PState sched
         inst_17 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_7 PState ->
       forall (j : Job) (t1 t : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_7
         inst_14
         inst_17 PState arr_seq sched JLFP j
         t1 ->
       @eq Nat
         (Prosa_Analysis_Definitions_Interference_cumulative_another_task_hep_job_interference Task
            inst_3 Job
            inst_7
            inst_10 PState arr_seq sched JLFP
            j t1 t)
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_other_task_hep_jobs Task
            inst_3 Job
            inst_7
            inst_10 PState arr_seq sched JLFP
            j t1 t)
```
