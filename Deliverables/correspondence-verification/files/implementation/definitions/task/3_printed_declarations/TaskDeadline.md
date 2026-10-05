# `TaskDeadline`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.definitions.task.TaskDeadline`
- Lean: `Prosa.Implementation.Definitions.Task.TaskDeadline`
- Certificate: `TaskDeadline_correspondence`

## Official Rocq

```coq
TaskDeadline :
concept.TaskDeadline
  (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)

TaskDeadline is not universe polymorphic
TaskDeadline is transparent
Expands to: Constant prosa.implementation.definitions.task.TaskDeadline
Declared in library prosa.implementation.definitions.task, line 137, characters 2-79
TaskDeadline
     : concept.TaskDeadline
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

Body:

```coq
TaskDeadline =
let Task := @reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task in
task_deadline
     : concept.TaskDeadline
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.TaskDeadline : Prosa.Model.Task.Concept.TaskDeadline
  Prosa.Implementation.Definitions.Task.concrete_task
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Definitions.Task.TaskDeadline : Prosa.Model.Task.Concept.TaskDeadline
  Prosa.Implementation.Definitions.Task.concrete_task :=
{ task_deadline := Prosa.Implementation.Definitions.Task.concrete_task.task_deadline }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_TaskDeadline
     : Prosa_Model_Task_Concept_TaskDeadline_inst1 Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```

Body:

```coq
Prosa_Implementation_Definitions_Task_TaskDeadline@{} =
Prosa_Model_Task_Concept_TaskDeadline_mk_inst1 Prosa_Implementation_Definitions_Task_concrete_task
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
  Prosa_Implementation_Definitions_Task_concrete_task_task_deadline
     : Prosa_Model_Task_Concept_TaskDeadline_inst1 Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```
