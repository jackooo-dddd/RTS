# `periodic_task_sets_respect_sporadic_task_model`

- Kind (Rocq): Remark
- Rocq: `prosa.model.task.arrival.periodic_as_sporadic.periodic_task_sets_respect_sporadic_task_model`
- Lean: `Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_task_sets_respect_sporadic_task_model`
- Certificate: `periodic_task_sets_respect_sporadic_task_model_correspondence`

## Official Rocq

```coq
periodic_task_sets_respect_sporadic_task_model :
forall {Task : TaskType} {H : PeriodicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall ts : TaskSet (Equality.sort Task),
@valid_periods Task H ts ->
@taskset_respects_periodic_task_model Task H Job H0 H1 arr_seq ts ->
@taskset_respects_sporadic_task_model Task (@periodic_as_sporadic Task H) ts Job H0 H1 arr_seq

periodic_task_sets_respect_sporadic_task_model is not universe polymorphic
Arguments periodic_task_sets_respect_sporadic_task_model {Task H Job H0 H1} arr_seq 
  H_valid_arrival_sequence ts _ _ tsk _ j j' _ _ _ _ _ _
periodic_task_sets_respect_sporadic_task_model is opaque
Expands to: Constant
            prosa.model.task.arrival.periodic_as_sporadic.periodic_task_sets_respect_sporadic_task_model
Declared in library prosa.model.task.arrival.periodic_as_sporadic, line 75, characters 9-55
@periodic_task_sets_respect_sporadic_task_model
     : forall (Task : TaskType) (H : PeriodicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall ts : TaskSet (Equality.sort Task),
       @valid_periods Task H ts ->
       @taskset_respects_periodic_task_model Task H Job H0 H1 arr_seq ts ->
       @taskset_respects_sporadic_task_model Task (@periodic_as_sporadic Task H) ts Job H0 H1 arr_seq
```

## Lean

```lean
@Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_task_sets_respect_sporadic_task_model : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Arrival.Periodic.valid_periods ts →
        Prosa.Model.Task.Arrival.Periodic.taskset_respects_periodic_task_model arr_seq ts →
          Prosa.Model.Task.Arrival.Sporadic.taskset_respects_sporadic_task_model ts arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_task_sets_respect_sporadic_task_model
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall ts : Prosa_Model_Task_Concept_TaskSet Task,
       Prosa_Model_Task_Arrival_Periodic_valid_periods Task
         inst_3
         inst_6 ts ->
       Prosa_Model_Task_Arrival_Periodic_taskset_respects_periodic_task_model Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq ts ->
       Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model Task
         inst_3
         (Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_as_sporadic Task
            inst_3
            inst_6)
         ts Job inst_10
         inst_13
         inst_17 arr_seq
```
