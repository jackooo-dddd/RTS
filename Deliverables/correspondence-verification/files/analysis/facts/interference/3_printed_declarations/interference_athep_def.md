# `interference_athep_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.interference_athep_def`
- Lean: `Prosa.Analysis.Facts.Interference.interference_athep_def`
- Certificate: `interference_athep_def_correspondence`

## Official Rocq

```coq
interference_athep_def :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job}
  {PState : ProcessorState Job},
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
@another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t =
@another_task_hep_job Task Job H0 JLFP j' j

interference_athep_def is not universe polymorphic
Arguments interference_athep_def {Task Job H0 H1 PState} H_uniprocessor_proc_model
  H_consumed_supply_proc_model arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute {JLFP} j t H_supply j' H_sched
interference_athep_def is opaque
Expands to: Constant prosa.analysis.facts.interference.interference_athep_def
Declared in library prosa.analysis.facts.interference, line 249, characters 12-34
@interference_athep_def
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (PState : ProcessorState Job),
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
       @another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t =
       @another_task_hep_job Task Job H0 JLFP j' j
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.interference_athep_def : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
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
                        Prosa.Analysis.Definitions.Interference.another_task_hep_job_interference arr_seq sched j t =
                          Prosa.Model.Priority.Definitions.another_task_hep_job j' j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_interference_athep_def
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
         inst_14 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_14 PState sched ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Supply_has_supply Job
            inst_7 PState sched t)
         Bool_true ->
       forall j' : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_7 PState sched j' t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_Interference_another_task_hep_job_interference Task
            inst_3 Job
            inst_7
            inst_10 PState arr_seq sched JLFP
            j t)
         (Prosa_Model_Priority_Definitions_another_task_hep_job Task
            inst_3 Job
            inst_7
            inst_10 JLFP j' j)
```
