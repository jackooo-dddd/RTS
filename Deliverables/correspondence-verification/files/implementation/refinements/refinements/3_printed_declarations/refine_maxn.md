# `refine_maxn`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_maxn`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_maxn`
- Certificate: `refine_maxn_correspondence`

## Official Rocq

```coq
refine_maxn : @refines (nat -> nat -> nat) (N -> N -> N) (Rnat ==> Rnat ==> Rnat) maxn (@maxn_T N lt_N)

refine_maxn is not universe polymorphic
refine_maxn is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_maxn
Declared in library prosa.implementation.refinements.refinements, line 146, characters 16-27
refine_maxn
     : @refines (nat -> nat -> nat) (N -> N -> N) (Rnat ==> Rnat ==> Rnat) maxn (@maxn_T N lt_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_maxn : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat))
  Nat.max Prosa.Implementation.Refinements.Refinements.maxn_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_maxn
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
         Nat_max
         (Prosa_Implementation_Refinements_Refinements_maxn_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_lt_N)
```
