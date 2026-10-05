# `schedulability_from_response_time_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.definitions.schedulability.schedulability_from_response_time_bound`
- Lean: `Prosa.Analysis.Definitions.Schedulability.schedulability_from_response_time_bound`
- Certificate: `schedulability_from_response_time_bound_correspondence`

## Official Rocq

```coq
schedulability_from_response_time_bound :
forall {Task : TaskType} {H : TaskDeadline Task} {Job : JobType} {H0 : JobArrival Job} 
  {H1 : JobCost Job} {H2 : JobTask Job Task} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (R : duration),
@task_response_time_bound Task Job H0 H1 H2 PState arr_seq sched tsk R ->
is_true (R <= @task_deadline Task H tsk) ->
@schedulable_task Task Job H1 (@absolute_deadline.job_deadline_from_task_deadline Job Task H H0 H2) H2 PState
  arr_seq sched tsk

schedulability_from_response_time_bound is not universe polymorphic
Arguments schedulability_from_response_time_bound {Task H Job H0 H1 H2 PState} arr_seq 
  sched tsk R H_response_time_bounded H_R_le_deadline j _ _
schedulability_from_response_time_bound is opaque
Expands to: Constant prosa.analysis.definitions.schedulability.schedulability_from_response_time_bound
Declared in library prosa.analysis.definitions.schedulability, line 89, characters 8-47
@schedulability_from_response_time_bound
     : forall (Task : TaskType) (H : TaskDeadline Task) (Job : JobType) (H0 : JobArrival Job)
         (H1 : JobCost Job) (H2 : JobTask Job Task) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (tsk : Equality.sort Task)
         (R : duration),
       @task_response_time_bound Task Job H0 H1 H2 PState arr_seq sched tsk R ->
       is_true (R <= @task_deadline Task H tsk) ->
       @schedulable_task Task Job H1 (@absolute_deadline.job_deadline_from_task_deadline Job Task H H0 H2) H2
         PState arr_seq sched tsk
```

## Lean

```lean
@Prosa.Analysis.Definitions.Schedulability.schedulability_from_response_time_bound : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Concept.TaskDeadline Task] {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (tsk : Task) (R : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched tsk R →
    R ≤ Prosa.Model.Task.Concept.task_deadline tsk →
      Prosa.Analysis.Definitions.Schedulability.schedulable_task arr_seq sched tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Schedulability_schedulability_from_response_time_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (inst_16 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (inst_19 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_10 PState)
         (tsk : Task) (R : Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_10
         inst_13
         inst_16
         inst_19 PState arr_seq sched
         tsk R ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat R
         (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
            inst_3
            inst_6 tsk) ->
       Prosa_Analysis_Definitions_Schedulability_schedulable_task Task
         inst_3 Job
         inst_10
         inst_16
         (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
            inst_10
            inst_3
            inst_6
            inst_13
            inst_19)
         inst_19 PState arr_seq sched
         tsk
```
