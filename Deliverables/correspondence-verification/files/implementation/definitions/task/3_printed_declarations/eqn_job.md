# `eqn_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.definitions.task.eqn_job`
- Lean: `Prosa.Implementation.Definitions.Task.eqn_job`
- Certificate: `eqn_job_correspondence`

## Official Rocq

```coq
eqn_job : Equality.axiom (T:=concrete_job) job_eqdef

eqn_job is not universe polymorphic
Arguments eqn_job x y
eqn_job is opaque
Expands to: Constant prosa.implementation.definitions.task.eqn_job
Declared in library prosa.implementation.definitions.task, line 98, characters 6-13
eqn_job
     : Equality.axiom (T:=concrete_job) job_eqdef
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.eqn_job : (x y : Prosa.Implementation.Definitions.Task.concrete_job) →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.BoolReflect (x = y)
    (Prosa.Implementation.Definitions.Task.job_eqdef x y)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_eqn_job
     : forall x y : Prosa_Implementation_Definitions_Task_concrete_job,
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect
         (@eq Prosa_Implementation_Definitions_Task_concrete_job x y)
         (Prosa_Implementation_Definitions_Task_job_eqdef x y)
```
