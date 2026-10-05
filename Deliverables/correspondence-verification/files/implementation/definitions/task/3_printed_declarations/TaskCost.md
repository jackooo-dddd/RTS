# `TaskCost`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.definitions.task.TaskCost`
- Lean: `Prosa.Implementation.Definitions.Task.TaskCost`
- Certificate: `TaskCost_correspondence`

## Official Rocq

```coq
TaskCost :
concept.TaskCost (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)

TaskCost is not universe polymorphic
TaskCost is transparent
Expands to: Constant prosa.implementation.definitions.task.TaskCost
Declared in library prosa.implementation.definitions.task, line 135, characters 2-67
TaskCost
     : concept.TaskCost
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

Body:

```coq
TaskCost =
let Task := @reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task in
task_cost
     : concept.TaskCost
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.TaskCost : Prosa.Model.Task.Concept.TaskCost
  Prosa.Implementation.Definitions.Task.concrete_task
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Definitions.Task.TaskCost : Prosa.Model.Task.Concept.TaskCost
  Prosa.Implementation.Definitions.Task.concrete_task :=
{ task_cost := Prosa.Implementation.Definitions.Task.concrete_task.task_cost }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_TaskCost
     : Prosa_Model_Task_Concept_TaskCost_inst1 Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```

Body:

```coq
Prosa_Implementation_Definitions_Task_TaskCost@{} =
Prosa_Model_Task_Concept_TaskCost_mk_inst1 Prosa_Implementation_Definitions_Task_concrete_task
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
  Prosa_Implementation_Definitions_Task_concrete_task_task_cost
     : Prosa_Model_Task_Concept_TaskCost_inst1 Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```
