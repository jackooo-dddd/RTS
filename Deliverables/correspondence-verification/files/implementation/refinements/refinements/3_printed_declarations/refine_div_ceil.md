# `refine_div_ceil`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_div_ceil`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_div_ceil`
- Certificate: `refine_div_ceil_correspondence`

## Official Rocq

```coq
refine_div_ceil :
@refines (nat -> nat -> nat) (N -> N -> N) (Rnat ==> Rnat ==> Rnat) div_ceil
  (@div_ceil_T N zero_N one_N add_N div_N mod_N eq_N)

refine_div_ceil is not universe polymorphic
refine_div_ceil is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_div_ceil
Declared in library prosa.implementation.refinements.refinements, line 112, characters 16-31
refine_div_ceil
     : @refines (nat -> nat -> nat) (N -> N -> N) (Rnat ==> Rnat ==> Rnat) div_ceil
         (@div_ceil_T N zero_N one_N add_N div_N mod_N eq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_div_ceil : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat))
  Prosa.Util.Div_mod.div_ceil Prosa.Implementation.Refinements.Refinements.div_ceil_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_div_ceil
     : Prosa_Implementation_Refinements_Refinements_refines (Nat -> Nat -> Nat)
         (Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N (Nat -> Nat)
            (Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_Refinements_Rnat
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat
               Prosa_Implementation_Refinements_Refinements_Rnat))
         Prosa_Util_Div_mod_div_ceil
         (Prosa_Implementation_Refinements_Refinements_div_ceil_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_eq_N)
```
