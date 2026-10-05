# `refine_b2n`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_b2n`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_b2n`
- Certificate: `refine_b2n_correspondence`

## Official Rocq

```coq
refine_b2n : @refines (N -> nat) (N -> N) (@unify N ==> Rnat) nat_of_bin id

refine_b2n is not universe polymorphic
refine_b2n is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_b2n
Declared in library prosa.implementation.refinements.refinements, line 86, characters 16-26
refine_b2n
     : @refines (N -> nat) (N -> N) (@unify N ==> Rnat) nat_of_bin id
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_b2n : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (fun x y => PLift (Prosa.Implementation.Refinements.Refinements.unify x y))
    Prosa.Implementation.Refinements.Refinements.Rnat)
  Prosa.Implementation.Refinements.Refinements.nat_of_bin id
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_b2n
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Refinements_N -> Nat)
         (Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_N Nat
            Prosa_Implementation_Refinements_Refinements_N
            (fun x y : Prosa_Implementation_Refinements_Refinements_N =>
             PLift_inst1
               (Prosa_Implementation_Refinements_Refinements_unify
                  Prosa_Implementation_Refinements_Refinements_N x y))
            Prosa_Implementation_Refinements_Refinements_Rnat)
         Prosa_Implementation_Refinements_Refinements_nat_of_bin
         (id Prosa_Implementation_Refinements_Refinements_N)
```
