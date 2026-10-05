# `refine_minn`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_minn`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_minn`
- Certificate: `refine_minn_correspondence`

## Official Rocq

```coq
refine_minn : @refines (nat -> nat -> nat) (N -> N -> N) (Rnat ==> Rnat ==> Rnat) minn (@minn_T N lt_N)

refine_minn is not universe polymorphic
refine_minn is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_minn
Declared in library prosa.implementation.refinements.refinements, line 130, characters 16-27
refine_minn
     : @refines (nat -> nat -> nat) (N -> N -> N) (Rnat ==> Rnat ==> Rnat) minn (@minn_T N lt_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_minn : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat))
  Nat.min Prosa.Implementation.Refinements.Refinements.minn_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_minn
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
         Nat_min
         (Prosa_Implementation_Refinements_Refinements_minn_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_lt_N)
```
