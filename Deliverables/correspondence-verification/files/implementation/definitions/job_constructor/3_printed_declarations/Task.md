# `Task`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.job_constructor.Task`
- Lean: `Prosa.Implementation.Definitions.JobConstructor.Task`
- Certificate: `Task_source_total, Task_target_total`

## Official Rocq

```coq
Task : eqType

Task is not universe polymorphic
Task is transparent
Expands to: Constant prosa.implementation.definitions.job_constructor.Task
Declared in library prosa.implementation.definitions.job_constructor, line 12, characters 11-15
Task
     : eqType
```

Body:

```coq
Task =
@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task
     : eqType
```

## Lean

```lean
Prosa.Implementation.Definitions.JobConstructor.Task : Type
```

Body:

```lean
@[reducible] def Prosa.Implementation.Definitions.JobConstructor.Task : Type :=
Prosa.Implementation.Definitions.Task.concrete_task
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_JobConstructor_Task
     : Type
```

Body:

```coq
Prosa_Implementation_Definitions_JobConstructor_Task@{} =
Prosa_Implementation_Definitions_Task_concrete_task
     : Type
```
