# `refine_get_arrival_curve_prefix'`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix'`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.refine_get_arrival_curve_prefix'`
- Certificate: `refine_get_arrival_curve_prefix'_correspondence`

## Official Rocq

```coq
refine_get_arrival_curve_prefix' :
forall tsk : @task_T binnat.N,
@refines (nat * seq (nat * nat)) (binnat.N * seq (binnat.N * binnat.N))
  (@prod_R nat binnat.N Rnat (seq (nat * nat)) (seq (binnat.N * binnat.N))
     (@list_R (nat * nat) (binnat.N * binnat.N) (@prod_R nat binnat.N Rnat nat binnat.N Rnat)))
  (get_arrival_curve_prefix (taskT_to_task tsk)) (@get_extrapolated_arrival_curve_T binnat.N one_N tsk)

refine_get_arrival_curve_prefix' is not universe polymorphic
Arguments refine_get_arrival_curve_prefix' tsk
refine_get_arrival_curve_prefix' is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix'
Declared in library prosa.implementation.refinements.arrival_curve, line 329, characters 18-50
refine_get_arrival_curve_prefix'
     : forall tsk : @task_T binnat.N,
       @refines (nat * seq (nat * nat)) (binnat.N * seq (binnat.N * binnat.N))
         (@prod_R nat binnat.N Rnat (seq (nat * nat)) (seq (binnat.N * binnat.N))
            (@list_R (nat * nat) (binnat.N * binnat.N) (@prod_R nat binnat.N Rnat nat binnat.N Rnat)))
         (get_arrival_curve_prefix (taskT_to_task tsk))
         (@get_extrapolated_arrival_curve_T binnat.N one_N tsk)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.refine_get_arrival_curve_prefix' : (tsk :
    Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Refinements.refines
    (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R
        (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
          Prosa.Implementation.Refinements.Refinements.Rnat)))
    (Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix
      (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))
    (Prosa.Implementation.Refinements.Task.get_extrapolated_arrival_curve_T tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_refine_get_arrival_curve_prefix'
     : forall
         tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N,
       Prosa_Implementation_Refinements_Refinements_refines
         (Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)))
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)))
         (Prosa_Implementation_Refinements_Refinements_prod_R Nat
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_Rnat
            (List_inst1 (Prod_inst3 Nat Nat))
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N))
            (Prosa_Implementation_Refinements_Refinements_list_R (Prod_inst3 Nat Nat)
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)
               (Prosa_Implementation_Refinements_Refinements_prod_R Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat)))
         (Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))
         (Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_one_N
            tsk)
```
