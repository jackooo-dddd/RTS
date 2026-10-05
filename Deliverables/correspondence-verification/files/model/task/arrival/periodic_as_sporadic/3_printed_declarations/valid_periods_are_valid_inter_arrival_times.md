# `valid_periods_are_valid_inter_arrival_times`

- Kind (Rocq): Remark
- Rocq: `prosa.model.task.arrival.periodic_as_sporadic.valid_periods_are_valid_inter_arrival_times`
- Lean: `Prosa.Model.Task.Arrival.PeriodicAsSporadic.valid_periods_are_valid_inter_arrival_times`
- Certificate: `valid_periods_are_valid_inter_arrival_times_correspondence`

## Official Rocq

```coq
valid_periods_are_valid_inter_arrival_times :
forall {Task : TaskType} {H : PeriodicModel Task} (ts : TaskSet (Equality.sort Task)),
@valid_periods Task H ts -> @valid_taskset_inter_arrival_times Task (@periodic_as_sporadic Task H) ts

valid_periods_are_valid_inter_arrival_times is not universe polymorphic
Arguments valid_periods_are_valid_inter_arrival_times {Task H} ts _ tsk _
valid_periods_are_valid_inter_arrival_times is opaque
Expands to: Constant
            prosa.model.task.arrival.periodic_as_sporadic.valid_periods_are_valid_inter_arrival_times
Declared in library prosa.model.task.arrival.periodic_as_sporadic, line 69, characters 9-52
@valid_periods_are_valid_inter_arrival_times
     : forall (Task : TaskType) (H : PeriodicModel Task) (ts : TaskSet (Equality.sort Task)),
       @valid_periods Task H ts -> @valid_taskset_inter_arrival_times Task (@periodic_as_sporadic Task H) ts
```

## Lean

```lean
@Prosa.Model.Task.Arrival.PeriodicAsSporadic.valid_periods_are_valid_inter_arrival_times : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Arrival.Periodic.valid_periods ts →
    Prosa.Model.Task.Arrival.Sporadic.valid_taskset_inter_arrival_times ts
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_PeriodicAsSporadic_valid_periods_are_valid_inter_arrival_times
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
       Prosa_Model_Task_Arrival_Periodic_valid_periods Task
         inst_3
         inst_6 ts ->
       Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times Task
         inst_3
         (Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_as_sporadic Task
            inst_3
            inst_6)
         ts
```
