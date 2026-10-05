# `eq_task`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.EDF.refinements.eq_task`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.eq_task`
- Certificate: `eq_task_correspondence`

## Official Rocq

```coq
eq_task : eq_of (@task_T N)

eq_task is not universe polymorphic
eq_task is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.eq_task
Declared in library prosa.implementation.refinements.EDF.refinements, line 182, characters 16-23
eq_task
     : eq_of (@task_T N)
```

Body:

```coq
eq_task = @task_eqdef_T N eq_N eq_taskab
     : eq_of (@task_T N)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.eq_task : Prosa.Implementation.Refinements.Refinements.eq_of
  (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N)
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Refinements.EDF.Refinements.eq_task : Prosa.Implementation.Refinements.Refinements.eq_of
  (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) :=
{ eq_op := Prosa.Implementation.Refinements.Task.task_eqdef_T }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_eq_task
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_eq_task@{} =
Prosa_Implementation_Refinements_Refinements_eq_of_mk
  (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
  (Prosa_Implementation_Refinements_Task_task_eqdef_T Prosa_Implementation_Refinements_Refinements_N
     Prosa_Implementation_Refinements_Refinements_eq_N
     Prosa_Implementation_Refinements_EDF_Refinements_eq_taskab)
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
```
