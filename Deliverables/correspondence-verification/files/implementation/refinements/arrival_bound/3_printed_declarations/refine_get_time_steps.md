# `refine_get_time_steps`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_bound.refine_get_time_steps`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.refine_get_time_steps`
- Certificate: `refine_get_time_steps_correspondence`

## Official Rocq

```coq
refine_get_time_steps :
@refines (nat * seq (nat * nat) -> seq nat) (N * seq (N * N) -> seq N)
  (@prod_R nat N Rnat (seq (nat * nat)) (seq (N * N))
     (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) ==>
   @list_R nat N Rnat)
  time_steps_of (@time_steps_of_T N)

refine_get_time_steps is not universe polymorphic
refine_get_time_steps is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.refine_get_time_steps
Declared in library prosa.implementation.refinements.arrival_bound, line 272, characters 18-39
refine_get_time_steps
     : @refines (nat * seq (nat * nat) -> seq nat) (N * seq (N * N) -> seq N)
         (@prod_R nat N Rnat (seq (nat * nat)) (seq (N * N))
            (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) ==>
          @list_R nat N Rnat)
         time_steps_of (@time_steps_of_T N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.refine_get_time_steps : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R
        (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
          Prosa.Implementation.Refinements.Refinements.Rnat)))
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat))
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of
  Prosa.Implementation.Refinements.ArrivalBound.time_steps_of_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_refine_get_time_steps
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)) -> List_inst1 Nat)
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)) ->
          List_inst1 Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            (Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)))
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               (List_inst1
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N)))
            (List_inst1 Nat) (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
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
            (Prosa_Implementation_Refinements_Refinements_list_R Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat))
         Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of
         (Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T
            Prosa_Implementation_Refinements_Refinements_N)
```
