# `refine_valid_arrivals`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_curve.refine_valid_arrivals`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.refine_valid_arrivals`
- Certificate: `refine_valid_arrivals_correspondence`

## Official Rocq

```coq
refine_valid_arrivals :
forall tsk : @task_T binnat.N,
@refines bool bool bool_R (valid_arrivals (taskT_to_task tsk))
  (@valid_arrivals_T binnat.N zero_N one_N eq_N leq_N lt_N tsk)

refine_valid_arrivals is not universe polymorphic
Arguments refine_valid_arrivals tsk
refine_valid_arrivals is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.refine_valid_arrivals
Declared in library prosa.implementation.refinements.arrival_curve, line 158, characters 18-39
refine_valid_arrivals
     : forall tsk : @task_T binnat.N,
       @refines bool bool bool_R (valid_arrivals (taskT_to_task tsk))
         (@valid_arrivals_T binnat.N zero_N one_N eq_N leq_N lt_N tsk)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.refine_valid_arrivals : (tsk :
    Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Refinements.refines Prosa.Implementation.Refinements.Refinements.bool_R
    (Prosa.Implementation.Refinements.ArrivalCurve.valid_arrivals
      (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))
    (Prosa.Implementation.Refinements.Task.valid_arrivals_T tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_refine_valid_arrivals
     : forall
         tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N,
       Prosa_Implementation_Refinements_Refinements_refines Bool Bool
         Prosa_Implementation_Refinements_Refinements_bool_R
         (Prosa_Implementation_Refinements_ArrivalCurve_valid_arrivals
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))
         (Prosa_Implementation_Refinements_Task_valid_arrivals_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_eq_N
            Prosa_Implementation_Refinements_Refinements_leq_N
            Prosa_Implementation_Refinements_Refinements_lt_N tsk)
```
