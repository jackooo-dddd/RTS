# `task_arrivals_bound_T`

- Kind (Rocq): Inductive
- Rocq: `prosa.implementation.refinements.arrival_bound.task_arrivals_bound_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T`
- Certificate: `task_arrivals_bound_T_source_total, task_arrivals_bound_T_target_total`

## Official Rocq

```coq
task_arrivals_bound_T : Type -> Type

task_arrivals_bound_T is not universe polymorphic
Arguments task_arrivals_bound_T {T}%_type_scope
Expands to: Inductive prosa.implementation.refinements.arrival_bound.task_arrivals_bound_T
Declared in library prosa.implementation.refinements.arrival_bound, line 27, characters 12-33
@task_arrivals_bound_T
     : Type -> Type
```

Body:

```coq
Inductive task_arrivals_bound_T (T : Type) : Type :=
    Periodic_T : T -> @task_arrivals_bound_T T
  | Sporadic_T : T -> @task_arrivals_bound_T T
  | ArrivalPrefix_T : T * seq (T * T) -> @task_arrivals_bound_T T.

Arguments task_arrivals_bound_T {T}%_type_scope
Arguments Periodic_T {T}%_type_scope _
Arguments Sporadic_T {T}%_type_scope _
Arguments ArrivalPrefix_T {T}%_type_scope _
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T : Type → Type
```

Body:

```lean
inductive Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T : Type → Type
number of parameters: 1
constructors:
Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Periodic_T : {T : Type} →
  T → Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T
Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Sporadic_T : {T : Type} →
  T → Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T
Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.ArrivalPrefix_T : {T : Type} →
  T × List (T × T) → Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
     : Type -> Type
```

Body:

```coq
Variant Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T@{} (A : Type) : Type :=
    Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Periodic_T : 
  A -> Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T A
  | Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Sporadic_T : 
  A -> Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T A
  | Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_ArrivalPrefix_T : 
  Prod_inst3 A (List_inst1 (Prod_inst3 A A)) ->
  Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T A.

Arguments Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T A%_type_scope
Arguments Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Periodic_T 
  A%_type_scope a____at____internal__hyg0
Arguments Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Sporadic_T 
  A%_type_scope a____at____internal__hyg0
Arguments Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_ArrivalPrefix_T 
  A%_type_scope a____at____internal__hyg0
```
