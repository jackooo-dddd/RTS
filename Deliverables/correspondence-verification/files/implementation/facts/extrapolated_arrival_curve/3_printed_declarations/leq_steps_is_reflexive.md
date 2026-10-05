# `leq_steps_is_reflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.leq_steps_is_reflexive`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.leq_steps_is_reflexive`
- Certificate: `facts_leq_steps_is_reflexive_certificate`

## Official Rocq

```coq
leq_steps_is_reflexive : @reflexive (nat * nat) leq_steps

leq_steps_is_reflexive is not universe polymorphic
Arguments leq_steps_is_reflexive x
leq_steps_is_reflexive is opaque
Expands to: Constant prosa.implementation.facts.extrapolated_arrival_curve.leq_steps_is_reflexive
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 19, characters 6-28
leq_steps_is_reflexive
     : @reflexive (nat * nat) leq_steps
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.leq_steps_is_reflexive : ∀ (a : ℕ × ℕ),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.leq_steps a a = true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_leq_steps_is_reflexive
     : forall a : Prod_inst3 Nat Nat,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps a a) Bool_true
```
