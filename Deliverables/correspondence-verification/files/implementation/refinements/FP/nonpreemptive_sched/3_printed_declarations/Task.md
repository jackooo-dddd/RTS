# `Task`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.nonpreemptive_sched.Task`
- Lean: `Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Task`
- Certificate: `Task_source_total, Task_target_total`

## Official Rocq

```coq
Task : eqType

Task is not universe polymorphic
Task is transparent
Expands to: Constant prosa.implementation.refinements.FP.nonpreemptive_sched.Task
Declared in library prosa.implementation.refinements.FP.nonpreemptive_sched, line 19, characters 13-17
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
Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Task : Type
```

Body:

```lean
@[reducible] def Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Task : Type :=
Prosa.Implementation.Definitions.Task.concrete_task
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Task
     : Type
```

Body:

```coq
Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Task@{} =
Prosa_Implementation_Definitions_Task_concrete_task
     : Type
```
