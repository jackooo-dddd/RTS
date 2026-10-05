# `TaskMaxInterArrival`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.task_max_inter_arrival.TaskMaxInterArrival`
- Lean: `Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival`
- Certificate: `TaskMaxInterArrival_source_total, TaskMaxInterArrival_target_total`

## Official Rocq

```coq
TaskMaxInterArrival : TaskType -> Type

TaskMaxInterArrival is not universe polymorphic
Arguments TaskMaxInterArrival Task
TaskMaxInterArrival is transparent
Expands to: Constant prosa.model.task.arrival.task_max_inter_arrival.TaskMaxInterArrival
Declared in library prosa.model.task.arrival.task_max_inter_arrival, line 8, characters 0-96
TaskMaxInterArrival
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
