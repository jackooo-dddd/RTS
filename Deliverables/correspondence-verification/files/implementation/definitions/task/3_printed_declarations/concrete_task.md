# `concrete_task`

- Kind (Rocq): Structure
- Rocq: `prosa.implementation.definitions.task.concrete_task`
- Lean: `Prosa.Implementation.Definitions.Task.concrete_task`
- Certificate: `concrete_task_source_total, concrete_task_target_total`

## Official Rocq

```coq
concrete_task : Type

concrete_task is not universe polymorphic
Expands to: Inductive prosa.implementation.definitions.task.concrete_task
Declared in library prosa.implementation.definitions.task, line 20, characters 10-23
concrete_task
     : Type
```

Body:

```coq
Record concrete_task : Type := Build_concrete_task
  { task_id : nat;
    task_cost : nat;
    task_arrival : task_arrivals_bound;
    task_deadline : instant;
    task_priority : nat }.

Arguments Build_concrete_task (task_id task_cost)%nat_scope task_arrival task_deadline
  task_priority%nat_scope
Arguments task_id c
Arguments task_cost c
Arguments task_arrival c
Arguments task_deadline c
Arguments task_priority c
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.concrete_task : Type
```

Body:

```lean
structure Prosa.Implementation.Definitions.Task.concrete_task : Type
number of parameters: 0
fields:
  Prosa.Implementation.Definitions.Task.concrete_task.task_id : ℕ
  Prosa.Implementation.Definitions.Task.concrete_task.task_cost : ℕ
  Prosa.Implementation.Definitions.Task.concrete_task.task_arrival : Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound
  Prosa.Implementation.Definitions.Task.concrete_task.task_deadline : Prosa.Behavior.Time.instant
  Prosa.Implementation.Definitions.Task.concrete_task.task_priority : ℕ
constructor:
  Prosa.Implementation.Definitions.Task.concrete_task.mk (task_id task_cost : ℕ)
    (task_arrival : Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound)
    (task_deadline : Prosa.Behavior.Time.instant) (task_priority : ℕ) :
    Prosa.Implementation.Definitions.Task.concrete_task
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_concrete_task
     : Type
```

Body:

```coq
Record
Prosa_Implementation_Definitions_Task_concrete_task@{}
    : Type := Prosa_Implementation_Definitions_Task_concrete_task_mk
  { task_id : Nat;
    task_cost : Nat;
    task_arrival : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound;
    task_deadline : Prosa_Behavior_Time_instant;
    task_priority : Nat } as default_proj_id.

Prosa_Implementation_Definitions_Task_concrete_task has primitive projections with eta conversion.
Arguments Prosa_Implementation_Definitions_Task_concrete_task_mk (task_id task_cost)%_Nat_scope 
  task_arrival task_deadline task_priority%_Nat_scope
```
