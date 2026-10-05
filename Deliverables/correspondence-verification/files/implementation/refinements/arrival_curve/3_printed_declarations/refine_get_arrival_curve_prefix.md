# `refine_get_arrival_curve_prefix`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.refine_get_arrival_curve_prefix`
- Certificate: `refine_get_arrival_curve_prefix_correspondence`

## Official Rocq

```coq
refine_get_arrival_curve_prefix :
@refines (Equality.sort Task -> nat * seq (nat * nat))
  (@task_T binnat.N -> binnat.N * seq (binnat.N * binnat.N))
  (Rtask ==>
   @prod_R nat binnat.N Rnat (seq (nat * nat)) (seq (binnat.N * binnat.N))
     (@list_R (nat * nat) (binnat.N * binnat.N) (@prod_R nat binnat.N Rnat nat binnat.N Rnat)))
  get_arrival_curve_prefix (@get_extrapolated_arrival_curve_T binnat.N one_N)

refine_get_arrival_curve_prefix is not universe polymorphic
refine_get_arrival_curve_prefix is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix
Declared in library prosa.implementation.refinements.arrival_curve, line 308, characters 18-49
refine_get_arrival_curve_prefix
     : @refines (Equality.sort Task -> nat * seq (nat * nat))
         (@task_T binnat.N -> binnat.N * seq (binnat.N * binnat.N))
         (Rtask ==>
          @prod_R nat binnat.N Rnat (seq (nat * nat)) (seq (binnat.N * binnat.N))
            (@list_R (nat * nat) (binnat.N * binnat.N) (@prod_R nat binnat.N Rnat nat binnat.N Rnat)))
         get_arrival_curve_prefix (@get_extrapolated_arrival_curve_T binnat.N one_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.refine_get_arrival_curve_prefix : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R
        (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
          Prosa.Implementation.Refinements.Refinements.Rnat))))
  Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix
  Prosa.Implementation.Refinements.Task.get_extrapolated_arrival_curve_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_refine_get_arrival_curve_prefix
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task -> Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)))
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)))
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
            (Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)))
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               (List_inst1
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N)))
            Prosa_Implementation_Refinements_Task_Rtask
            (Prosa_Implementation_Refinements_Refinements_prod_R Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat (List_inst1 (Prod_inst3 Nat Nat))
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
                     Prosa_Implementation_Refinements_Refinements_Rnat))))
         Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix
         (Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_one_N)
```
