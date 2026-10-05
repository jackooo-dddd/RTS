# `posBinNatNotZero`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.refinements.posBinNatNotZero`
- Lean: `Prosa.Implementation.Refinements.Refinements.posBinNatNotZero`
- Certificate: `posBinNatNotZero_correspondence`

## Official Rocq

```coq
posBinNatNotZero : forall p : positive, nat_of_bin (N.pos p) <> 0

posBinNatNotZero is not universe polymorphic
Arguments posBinNatNotZero p%_positive_scope _
posBinNatNotZero is opaque
Expands to: Constant prosa.implementation.refinements.refinements.posBinNatNotZero
Declared in library prosa.implementation.refinements.refinements, line 168, characters 6-22
posBinNatNotZero
     : forall p : positive, nat_of_bin (N.pos p) <> 0
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.posBinNatNotZero : ∀
  (p : Prosa.Implementation.Refinements.Refinements.positive),
  Prosa.Implementation.Refinements.Refinements.nat_of_bin (Prosa.Implementation.Refinements.Refinements.N.Npos p) ≠ 0
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_posBinNatNotZero
     : forall p : Prosa_Implementation_Refinements_Refinements_positive,
       Ne Nat
         (Prosa_Implementation_Refinements_Refinements_nat_of_bin
            (Prosa_Implementation_Refinements_Refinements_N_Npos p))
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
