# `refine_arrival_curve_prefix`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_bound.refine_arrival_curve_prefix`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.refine_arrival_curve_prefix`
- Certificate: `refine_arrival_curve_prefix_correspondence`

## Official Rocq

```coq
refine_arrival_curve_prefix :
@refines (nat * seq (nat * nat) -> nat -> nat) (N * seq (N * N) -> N -> N)
  (@prod_R nat N Rnat (seq (nat * nat)) (seq (N * N))
     (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) ==>
   Rnat ==> Rnat)
  extrapolated_arrival_curve (@extrapolated_arrival_curve_T N zero_N add_N mul_N div_N mod_N leq_N)

refine_arrival_curve_prefix is not universe polymorphic
refine_arrival_curve_prefix is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.refine_arrival_curve_prefix
Declared in library prosa.implementation.refinements.arrival_bound, line 282, characters 18-45
refine_arrival_curve_prefix
     : @refines (nat * seq (nat * nat) -> nat -> nat) (N * seq (N * N) -> N -> N)
         (@prod_R nat N Rnat (seq (nat * nat)) (seq (N * N))
            (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) ==>
          Rnat ==> Rnat)
         extrapolated_arrival_curve (@extrapolated_arrival_curve_T N zero_N add_N mul_N div_N mod_N leq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.refine_arrival_curve_prefix : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R
        (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
          Prosa.Implementation.Refinements.Refinements.Rnat)))
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat))
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve
  Prosa.Implementation.Refinements.ArrivalBound.extrapolated_arrival_curve_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_refine_arrival_curve_prefix
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
         Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve
         (Prosa_Implementation_Refinements_ArrivalBound_extrapolated_arrival_curve_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N)
```
