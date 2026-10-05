# `ltn_steps_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.ltn_steps_is_transitive`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.ltn_steps_is_transitive`
- Certificate: `facts_ltn_steps_is_transitive_certificate`

## Official Rocq

```coq
ltn_steps_is_transitive : @transitive (nat * nat) ltn_steps

ltn_steps_is_transitive is not universe polymorphic
Arguments ltn_steps_is_transitive y x z _ _
ltn_steps_is_transitive is opaque
Expands to: Constant prosa.implementation.facts.extrapolated_arrival_curve.ltn_steps_is_transitive
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 11, characters 6-29
ltn_steps_is_transitive
     : @transitive (nat * nat) ltn_steps
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.ltn_steps_is_transitive : ∀ (a b c : ℕ × ℕ),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ltn_steps a b = true →
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ltn_steps b c = true →
      Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ltn_steps a c = true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_ltn_steps_is_transitive
     : forall a b c : Prod_inst3 Nat Nat,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps a b) Bool_true ->
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps b c) Bool_true ->
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps a c) Bool_true
```
