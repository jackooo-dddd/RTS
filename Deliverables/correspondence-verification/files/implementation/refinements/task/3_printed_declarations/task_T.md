# `task_T`

- Kind (Rocq): Structure
- Rocq: `prosa.implementation.refinements.task.task_T`
- Lean: `Prosa.Implementation.Refinements.Task.task_T`
- Certificate: `task_T_source_total, task_T_target_total`

## Official Rocq

```coq
task_T : Type -> Type

task_T is not universe polymorphic
Arguments task_T {T}%_type_scope
Expands to: Inductive prosa.implementation.refinements.task.task_T
Declared in library prosa.implementation.refinements.task, line 29, characters 12-18
@task_T
     : Type -> Type
```

Body:

```coq
Record task_T (T : Type) : Type := Build_task_T
  { task_id_T : T;
    task_cost_T : T;
    task_arrival_T : @task_arrivals_bound_T T;
    task_deadline_T : T;
    task_priority_T : T }.

Arguments task_T {T}%_type_scope
Arguments Build_task_T {T}%_type_scope task_id_T task_cost_T task_arrival_T task_deadline_T task_priority_T
Arguments task_id_T {T}%_type_scope t
Arguments task_cost_T {T}%_type_scope t
Arguments task_arrival_T {T}%_type_scope t
Arguments task_deadline_T {T}%_type_scope t
Arguments task_priority_T {T}%_type_scope t
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.task_T : Type → Type
```

Body:

```lean
structure Prosa.Implementation.Refinements.Task.task_T (T : Type) : Type
number of parameters: 1
fields:
  Prosa.Implementation.Refinements.Task.task_T.task_id_T : T
  Prosa.Implementation.Refinements.Task.task_T.task_cost_T : T
  Prosa.Implementation.Refinements.Task.task_T.task_arrival_T : Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T
      T
  Prosa.Implementation.Refinements.Task.task_T.task_deadline_T : T
  Prosa.Implementation.Refinements.Task.task_T.task_priority_T : T
constructor:
  Prosa.Implementation.Refinements.Task.task_T.mk {T : Type} (task_id_T task_cost_T : T)
    (task_arrival_T : Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T)
    (task_deadline_T task_priority_T : T) : Prosa.Implementation.Refinements.Task.task_T T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_task_T
     : Type -> Type
```

Body:

```coq
Record
Prosa_Implementation_Refinements_Task_task_T@{} (A : Type)
  : Type := Prosa_Implementation_Refinements_Task_task_T_mk
  { task_id_T : A;
    task_cost_T : A;
    task_arrival_T : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T A;
    task_deadline_T : A;
    task_priority_T : A } as default_proj_id.

Prosa_Implementation_Refinements_Task_task_T has primitive projections with eta conversion.
Arguments Prosa_Implementation_Refinements_Task_task_T A%_type_scope
Arguments Prosa_Implementation_Refinements_Task_task_T_mk A%_type_scope task_id_T 
  task_cost_T task_arrival_T task_deadline_T task_priority_T
```
