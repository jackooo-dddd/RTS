# `refine_dvdn`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_dvdn`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_dvdn`
- Certificate: `refine_dvdn_correspondence`

## Official Rocq

```coq
refine_dvdn :
@refines (nat -> nat -> bool) (N -> N -> bool) (Rnat ==> Rnat ==> bool_R) dvdn (@dvdn_T N zero_N mod_N eq_N)

refine_dvdn is not universe polymorphic
refine_dvdn is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_dvdn
Declared in library prosa.implementation.refinements.refinements, line 104, characters 16-27
refine_dvdn
     : @refines (nat -> nat -> bool) (N -> N -> bool) (Rnat ==> Rnat ==> bool_R) dvdn
         (@dvdn_T N zero_N mod_N eq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_dvdn : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.bool_R))
  (fun d m => decide (d ∣ m)) Prosa.Implementation.Refinements.Refinements.dvdn_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_dvdn
     : Prosa_Implementation_Refinements_Refinements_refines (Nat -> Nat -> Bool)
         (Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N -> Bool)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N (Nat -> Bool)
            (Prosa_Implementation_Refinements_Refinements_N -> Bool)
            Prosa_Implementation_Refinements_Refinements_Rnat
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N Bool Bool
               Prosa_Implementation_Refinements_Refinements_Rnat
               Prosa_Implementation_Refinements_Refinements_bool_R))
         (fun d m : Nat => Decidable_decide (Dvd_dvd_inst1 Nat Nat_instDvd d m) (Nat_decidable_dvd d m))
         (Prosa_Implementation_Refinements_Refinements_dvdn_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_eq_N)
```
