# `refine_value_at`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_bound.refine_value_at`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.refine_value_at`
- Certificate: `refine_value_at_correspondence`

## Official Rocq

```coq
refine_value_at :
@refines (nat * seq (nat * nat) -> nat -> nat) (N * seq (N * N) -> N -> N)
  (@prod_R nat N Rnat (seq (nat * nat)) (seq (N * N))
     (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) ==>
   Rnat ==> Rnat)
  value_at (@value_at_T N zero_N leq_N)

refine_value_at is not universe polymorphic
refine_value_at is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.refine_value_at
Declared in library prosa.implementation.refinements.arrival_bound, line 252, characters 18-33
refine_value_at
     : @refines (nat * seq (nat * nat) -> nat -> nat) (N * seq (N * N) -> N -> N)
         (@prod_R nat N Rnat (seq (nat * nat)) (seq (N * N))
            (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) ==>
          Rnat ==> Rnat)
         value_at (@value_at_T N zero_N leq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.refine_value_at : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R
        (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
          Prosa.Implementation.Refinements.Refinements.Rnat)))
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat))
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at
  Prosa.Implementation.Refinements.ArrivalBound.value_at_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_refine_value_at
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)) -> Nat -> Nat)
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)) ->
          Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            (Prod_inst3 Nat (List_inst1 (Prod_inst3 Nat Nat)))
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               (List_inst1
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N)))
            (Nat -> Nat)
            (Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
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
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat
               Prosa_Implementation_Refinements_Refinements_Rnat))
         Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at
         (Prosa_Implementation_Refinements_ArrivalBound_value_at_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_leq_N)
```
