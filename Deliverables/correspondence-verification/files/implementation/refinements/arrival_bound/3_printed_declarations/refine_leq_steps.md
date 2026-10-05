# `refine_leq_steps`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_bound.refine_leq_steps`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.refine_leq_steps`
- Certificate: `refine_leq_steps_correspondence`

## Official Rocq

```coq
refine_leq_steps :
@refines (nat * nat -> nat * nat -> bool) (N * N -> N * N -> bool)
  (@prod_R nat N Rnat nat N Rnat ==> @prod_R nat N Rnat nat N Rnat ==> bool_R) leq_steps
  (@leq_steps_T N leq_N)

refine_leq_steps is not universe polymorphic
refine_leq_steps is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.refine_leq_steps
Declared in library prosa.implementation.refinements.arrival_bound, line 179, characters 18-34
refine_leq_steps
     : @refines (nat * nat -> nat * nat -> bool) (N * N -> N * N -> bool)
         (@prod_R nat N Rnat nat N Rnat ==> @prod_R nat N Rnat nat N Rnat ==> bool_R) leq_steps
         (@leq_steps_T N leq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.refine_leq_steps : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat)
    (Prosa.Implementation.Refinements.Refinements.hrespectful
      (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
        Prosa.Implementation.Refinements.Refinements.Rnat)
      Prosa.Implementation.Refinements.Refinements.bool_R))
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.leq_steps
  Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_refine_leq_steps
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prod_inst3 Nat Nat -> Prod_inst3 Nat Nat -> Bool)
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N ->
          Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N ->
          Bool)
         (Prosa_Implementation_Refinements_Refinements_hrespectful (Prod_inst3 Nat Nat)
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N)
            (Prod_inst3 Nat Nat -> Bool)
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N ->
             Bool)
            (Prosa_Implementation_Refinements_Refinements_prod_R Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat)
            (Prosa_Implementation_Refinements_Refinements_hrespectful (Prod_inst3 Nat Nat)
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)
               Bool Bool
               (Prosa_Implementation_Refinements_Refinements_prod_R Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat)
               Prosa_Implementation_Refinements_Refinements_bool_R))
         Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps
         (Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_leq_N)
```
