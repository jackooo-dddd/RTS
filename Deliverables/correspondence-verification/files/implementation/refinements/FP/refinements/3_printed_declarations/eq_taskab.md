# `eq_taskab`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.eq_taskab`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.eq_taskab`
- Certificate: `eq_taskab_correspondence`

## Official Rocq

```coq
eq_taskab : eq_of (@task_arrivals_bound_T N)

eq_taskab is not universe polymorphic
eq_taskab is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.eq_taskab
Declared in library prosa.implementation.refinements.FP.refinements, line 156, characters 16-25
eq_taskab
     : eq_of (@task_arrivals_bound_T N)
```

Body:

```coq
eq_taskab = @taskab_eqdef_T N eq_N eq_NlistNN
     : eq_of (@task_arrivals_bound_T N)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.eq_taskab : Prosa.Implementation.Refinements.Refinements.eq_of
  (Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T Prosa.Implementation.Refinements.Refinements.N)
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Refinements.FP.Refinements.eq_taskab : Prosa.Implementation.Refinements.Refinements.eq_of
  (Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T
    Prosa.Implementation.Refinements.Refinements.N) :=
{ eq_op := Prosa.Implementation.Refinements.ArrivalBound.taskab_eqdef_T }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_eq_taskab
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
            Prosa_Implementation_Refinements_Refinements_N)
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_eq_taskab@{} =
Prosa_Implementation_Refinements_Refinements_eq_of_mk
  (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
     Prosa_Implementation_Refinements_Refinements_N)
  (Prosa_Implementation_Refinements_ArrivalBound_taskab_eqdef_T
     Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_eq_N
     Prosa_Implementation_Refinements_FP_Refinements_eq_NlistNN)
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
            Prosa_Implementation_Refinements_Refinements_N)
```
