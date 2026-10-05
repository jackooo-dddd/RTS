# `Rtask`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.Rtask`
- Lean: `Prosa.Implementation.Refinements.Task.Rtask`
- Certificate: `Rtask_correspondence`

## Official Rocq

```coq
Rtask : Equality.sort Task -> @task_T binnat.N -> Type

Rtask is not universe polymorphic
Rtask is transparent
Expands to: Constant prosa.implementation.refinements.task.Rtask
Declared in library prosa.implementation.refinements.task, line 118, characters 11-16
Rtask
     : Equality.sort Task -> @task_T binnat.N -> Type
```

Body:

```coq
Rtask =
@fun_hrel (Equality.sort Task) (@task_T binnat.N) taskT_to_task
     : Equality.sort Task -> @task_T binnat.N -> Type
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.Rtask : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N → Type
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.Rtask : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N → Type :=
Prosa.Implementation.Refinements.Refinements.fun_hrel Prosa.Implementation.Refinements.Task.taskT_to_task
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_Rtask
     : Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N -> Type
```

Body:

```coq
Prosa_Implementation_Refinements_Task_Rtask@{} =
Prosa_Implementation_Refinements_Refinements_fun_hrel Prosa_Implementation_Refinements_Task_Task
  (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
  Prosa_Implementation_Refinements_Task_taskT_to_task
     : Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N -> Type

Arguments Prosa_Implementation_Refinements_Task_Rtask a____at____internal__hyg0 a____at____internal__hyg0
```
