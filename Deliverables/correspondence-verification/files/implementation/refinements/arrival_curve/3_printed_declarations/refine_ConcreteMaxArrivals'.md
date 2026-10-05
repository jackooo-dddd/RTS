# `refine_ConcreteMaxArrivals'`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_curve.refine_ConcreteMaxArrivals'`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.refine_ConcreteMaxArrivals'`
- Certificate: `refine_ConcreteMaxArrivals'_correspondence`

## Official Rocq

```coq
refine_ConcreteMaxArrivals' :
forall tsk : @task_T binnat.N,
@refines (nat -> nat) (binnat.N -> binnat.N) (Rnat ==> Rnat) (ConcreteMaxArrivals (taskT_to_task tsk))
  (@ConcreteMaxArrivals_T binnat.N zero_N one_N add_N mul_N div_N mod_N leq_N tsk)

refine_ConcreteMaxArrivals' is not universe polymorphic
Arguments refine_ConcreteMaxArrivals' tsk
refine_ConcreteMaxArrivals' is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.refine_ConcreteMaxArrivals'
Declared in library prosa.implementation.refinements.arrival_curve, line 284, characters 18-45
refine_ConcreteMaxArrivals'
     : forall tsk : @task_T binnat.N,
       @refines (nat -> nat) (binnat.N -> binnat.N) (Rnat ==> Rnat) (ConcreteMaxArrivals (taskT_to_task tsk))
         (@ConcreteMaxArrivals_T binnat.N zero_N one_N add_N mul_N div_N mod_N leq_N tsk)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.refine_ConcreteMaxArrivals' : (tsk :
    Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Refinements.refines
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat)
    (Prosa.Model.Task.Arrival.Curves.max_arrivals (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))
    (Prosa.Implementation.Refinements.Task.ConcreteMaxArrivals_T tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_refine_ConcreteMaxArrivals'
     : forall
         tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N,
       Prosa_Implementation_Refinements_Refinements_refines (Nat -> Nat)
         (Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N Nat Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_Rnat
            Prosa_Implementation_Refinements_Refinements_Rnat)
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals_inst1
            Prosa_Implementation_Definitions_Task_concrete_task
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
            Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))
         (Prosa_Implementation_Refinements_Task_ConcreteMaxArrivals_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N tsk)
```
