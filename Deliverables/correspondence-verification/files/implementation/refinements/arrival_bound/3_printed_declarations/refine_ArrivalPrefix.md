# `refine_ArrivalPrefix`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_bound.refine_ArrivalPrefix`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.refine_ArrivalPrefix`
- Certificate: `refine_ArrivalPrefix_correspondence`

## Official Rocq

```coq
refine_ArrivalPrefix :
@refines (nat * seq (nat * nat) -> task_arrivals_bound) (N * seq (N * N) -> @task_arrivals_bound_T N)
  (@prod_R nat N Rnat (seq (nat * nat)) (seq (N * N))
     (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) ==>
   Rtask_ab)
  ArrivalPrefix (@ArrivalPrefix_T N)

refine_ArrivalPrefix is not universe polymorphic
refine_ArrivalPrefix is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.refine_ArrivalPrefix
Declared in library prosa.implementation.refinements.arrival_bound, line 291, characters 18-38
refine_ArrivalPrefix
     : @refines (nat * seq (nat * nat) -> task_arrivals_bound) (N * seq (N * N) -> @task_arrivals_bound_T N)
         (@prod_R nat N Rnat (seq (nat * nat)) (seq (N * N))
            (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) ==>
          Rtask_ab)
         ArrivalPrefix (@ArrivalPrefix_T N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.refine_ArrivalPrefix : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R
        (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
          Prosa.Implementation.Refinements.Refinements.Rnat)))
    Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab)
  Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.ArrivalPrefix
  Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.ArrivalPrefix_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_refine_ArrivalPrefix
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)) ->
          Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound)
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)) ->
          Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
            Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            (Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)))
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               (List_inst1
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N)))
            Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
            (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
               Prosa_Implementation_Refinements_Refinements_N)
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
                     Prosa_Implementation_Refinements_Refinements_Rnat)))
            Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab)
         Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
         (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_ArrivalPrefix_T
            Prosa_Implementation_Refinements_Refinements_N)
```
