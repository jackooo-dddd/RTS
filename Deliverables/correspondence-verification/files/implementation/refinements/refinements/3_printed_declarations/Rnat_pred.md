# `Rnat_pred`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.Rnat_pred`
- Lean: `Prosa.Implementation.Refinements.Refinements.Rnat_pred`
- Certificate: `Rnat_pred_correspondence`

## Official Rocq

```coq
Rnat_pred : @refines (nat -> nat) (N -> N) (Rnat ==> Rnat) predn (@predn_T N one_N sub_N)

Rnat_pred is not universe polymorphic
Rnat_pred is opaque
Expands to: Constant prosa.implementation.refinements.refinements.Rnat_pred
Declared in library prosa.implementation.refinements.refinements, line 95, characters 16-25
Rnat_pred
     : @refines (nat -> nat) (N -> N) (Rnat ==> Rnat) predn (@predn_T N one_N sub_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.Rnat_pred : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    Prosa.Implementation.Refinements.Refinements.Rnat)
  Nat.pred Prosa.Implementation.Refinements.Refinements.predn_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_Rnat_pred
     : Prosa_Implementation_Refinements_Refinements_refines (Nat -> Nat)
         (Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N Nat Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_Rnat
            Prosa_Implementation_Refinements_Refinements_Rnat)
         Nat_pred
         (Prosa_Implementation_Refinements_Refinements_predn_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_sub_N)
```
