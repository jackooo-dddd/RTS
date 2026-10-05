# `periodic_task_respects_sporadic_task_model`

- Kind (Rocq): Remark
- Rocq: `prosa.model.task.arrival.periodic_as_sporadic.periodic_task_respects_sporadic_task_model`
- Lean: `Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_task_respects_sporadic_task_model`
- Certificate: `periodic_task_respects_sporadic_task_model_correspondence`

## Official Rocq

```coq
periodic_task_respects_sporadic_task_model :
forall {Task : TaskType} {H : PeriodicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
is_true (@valid_period Task H tsk) ->
@respects_periodic_task_model Task H Job H0 H1 arr_seq tsk ->
@respects_sporadic_task_model Task (@periodic_as_sporadic Task H) Job H0 H1 arr_seq tsk

periodic_task_respects_sporadic_task_model is not universe polymorphic
Arguments periodic_task_respects_sporadic_task_model {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  tsk _ _ j j' _ _ _ _ _ _
periodic_task_respects_sporadic_task_model is opaque
Expands to: Constant prosa.model.task.arrival.periodic_as_sporadic.periodic_task_respects_sporadic_task_model
Declared in library prosa.model.task.arrival.periodic_as_sporadic, line 40, characters 9-51
@periodic_task_respects_sporadic_task_model
     : forall (Task : TaskType) (H : PeriodicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       is_true (@valid_period Task H tsk) ->
       @respects_periodic_task_model Task H Job H0 H1 arr_seq tsk ->
       @respects_sporadic_task_model Task (@periodic_as_sporadic Task H) Job H0 H1 arr_seq tsk
```

## Lean

```lean
@Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_task_respects_sporadic_task_model : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
        Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
          Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_task_respects_sporadic_task_model
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
       forall tsk : Task,
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk ->
       Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model Task
         inst_3
         (Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_as_sporadic Task
            inst_3
            inst_6)
         Job inst_10
         inst_13
         inst_17 arr_seq tsk
```
