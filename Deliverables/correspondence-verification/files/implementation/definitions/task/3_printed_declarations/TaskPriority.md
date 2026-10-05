# `TaskPriority`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.definitions.task.TaskPriority`
- Lean: `Prosa.Implementation.Definitions.Task.TaskPriority`
- Certificate: `TaskPriority_correspondence`

## Official Rocq

```coq
TaskPriority :
numeric_fixed_priority.TaskPriority
  (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)

TaskPriority is not universe polymorphic
TaskPriority is transparent
Expands to: Constant prosa.implementation.definitions.task.TaskPriority
Declared in library prosa.implementation.definitions.task, line 136, characters 2-79
TaskPriority
     : numeric_fixed_priority.TaskPriority
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

Body:

```coq
TaskPriority =
let Task := @reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task in
task_priority
     : numeric_fixed_priority.TaskPriority
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.TaskPriority : Prosa.Model.Priority.NumericFixedPriority.TaskPriority
  Prosa.Implementation.Definitions.Task.concrete_task
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Definitions.Task.TaskPriority : Prosa.Model.Priority.NumericFixedPriority.TaskPriority
  Prosa.Implementation.Definitions.Task.concrete_task :=
{ task_priority := Prosa.Implementation.Definitions.Task.concrete_task.task_priority }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_TaskPriority
     : Prosa_Model_Priority_NumericFixedPriority_TaskPriority_inst1
         Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```

Body:

```coq
Prosa_Implementation_Definitions_Task_TaskPriority@{} =
Prosa_Model_Priority_NumericFixedPriority_TaskPriority_mk_inst1
  Prosa_Implementation_Definitions_Task_concrete_task
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
  Prosa_Implementation_Definitions_Task_concrete_task_task_priority
     : Prosa_Model_Priority_NumericFixedPriority_TaskPriority_inst1
         Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```
