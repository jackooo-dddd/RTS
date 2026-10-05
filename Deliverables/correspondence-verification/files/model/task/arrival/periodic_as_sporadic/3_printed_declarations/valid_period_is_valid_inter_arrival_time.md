# `valid_period_is_valid_inter_arrival_time`

- Kind (Rocq): Remark
- Rocq: `prosa.model.task.arrival.periodic_as_sporadic.valid_period_is_valid_inter_arrival_time`
- Lean: `Prosa.Model.Task.Arrival.PeriodicAsSporadic.valid_period_is_valid_inter_arrival_time`
- Certificate: `valid_period_is_valid_inter_arrival_time_correspondence`

## Official Rocq

```coq
valid_period_is_valid_inter_arrival_time :
forall {Task : TaskType} {H : PeriodicModel Task} (tsk : Equality.sort Task),
is_true (@valid_period Task H tsk) ->
is_true (@valid_task_min_inter_arrival_time Task (@periodic_as_sporadic Task H) tsk)

valid_period_is_valid_inter_arrival_time is not universe polymorphic
Arguments valid_period_is_valid_inter_arrival_time {Task H} tsk _
valid_period_is_valid_inter_arrival_time is opaque
Expands to: Constant prosa.model.task.arrival.periodic_as_sporadic.valid_period_is_valid_inter_arrival_time
Declared in library prosa.model.task.arrival.periodic_as_sporadic, line 31, characters 9-49
@valid_period_is_valid_inter_arrival_time
     : forall (Task : TaskType) (H : PeriodicModel Task) (tsk : Equality.sort Task),
       is_true (@valid_period Task H tsk) ->
       is_true (@valid_task_min_inter_arrival_time Task (@periodic_as_sporadic Task H) tsk)
```

## Lean

```lean
@Prosa.Model.Task.Arrival.PeriodicAsSporadic.valid_period_is_valid_inter_arrival_time : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] (tsk : Task),
  Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
    Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time tsk = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_PeriodicAsSporadic_valid_period_is_valid_inter_arrival_time
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (tsk : Task),
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time Task
            inst_3
            (Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_as_sporadic Task
               inst_3
               inst_6)
            tsk)
         Bool_true
```
