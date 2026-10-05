# `eqn_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.definitions.task.eqn_task`
- Lean: `Prosa.Implementation.Definitions.Task.eqn_task`
- Certificate: `eqn_task_correspondence`

## Official Rocq

```coq
eqn_task : Equality.axiom (T:=concrete_task) task_eqdef

eqn_task is not universe polymorphic
Arguments eqn_task x y
eqn_task is opaque
Expands to: Constant prosa.implementation.definitions.task.eqn_task
Declared in library prosa.implementation.definitions.task, line 38, characters 6-14
eqn_task
     : Equality.axiom (T:=concrete_task) task_eqdef
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.eqn_task : (x y : Prosa.Implementation.Definitions.Task.concrete_task) →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.BoolReflect (x = y)
    (Prosa.Implementation.Definitions.Task.task_eqdef x y)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_eqn_task
     : forall x y : Prosa_Implementation_Definitions_Task_concrete_task,
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect
         (@eq Prosa_Implementation_Definitions_Task_concrete_task x y)
         (Prosa_Implementation_Definitions_Task_task_eqdef x y)
```
