# `slowed_is_unit_step`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.unit_growth.slowed_is_unit_step`
- Lean: `Prosa.Util.UnitGrowth.slowed_is_unit_step`
- Certificate: `slowed_is_unit_step_statement_certificate`

## Official Rocq

```coq
slowed_is_unit_step : forall f : nat -> nat, unit_growth_function (slowed f)

slowed_is_unit_step is not universe polymorphic
Arguments slowed_is_unit_step f%function_scope t
slowed_is_unit_step is opaque
Expands to: Constant prosa.util.unit_growth.slowed_is_unit_step
Declared in library prosa.util.unit_growth, line 214, characters 6-25
slowed_is_unit_step
     : forall f : nat -> nat, unit_growth_function (slowed f)
```

## Lean

```lean
Prosa.Util.UnitGrowth.slowed_is_unit_step : ∀ (f : ℕ → ℕ),
  Prosa.Util.UnitGrowth.unit_growth_function (Prosa.Util.UnitGrowth.slowed f)
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_slowed_is_unit_step
     : forall f : Nat -> Nat, Prosa_Util_UnitGrowth_unit_growth_function (Prosa_Util_UnitGrowth_slowed f)
```
