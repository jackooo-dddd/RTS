# `unit_growth_function`

- Kind (Rocq): Definition
- Rocq: `prosa.util.unit_growth.unit_growth_function`
- Lean: `Prosa.Util.UnitGrowth.unit_growth_function`
- Certificate: `ug_unit_growth_correspondence`

## Official Rocq

```coq
unit_growth_function : (nat -> nat) -> Prop

unit_growth_function is not universe polymorphic
Arguments unit_growth_function f%function_scope
unit_growth_function is transparent
Expands to: Constant prosa.util.unit_growth.unit_growth_function
Declared in library prosa.util.unit_growth, line 6, characters 11-31
unit_growth_function
     : (nat -> nat) -> Prop
```

Body:

```coq
unit_growth_function =
fun f : nat -> nat => forall t : nat, is_true (f (t + 1) <= f t + 1)
     : (nat -> nat) -> Prop

Arguments unit_growth_function f%function_scope
```

## Lean

```lean
Prosa.Util.UnitGrowth.unit_growth_function : (ℕ → ℕ) → Prop
```

Body:

```lean
def Prosa.Util.UnitGrowth.unit_growth_function : (ℕ → ℕ) → Prop :=
fun f => ∀ (t : ℕ), f (t + 1) ≤ f t + 1
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_unit_growth_function
     : (Nat -> Nat) -> SProp
```

Body:

```coq
Prosa_Util_UnitGrowth_unit_growth_function@{} =
fun f : Nat -> Nat =>
forall t : Nat,
LE_le_inst1 Nat instLENat
  (f
     (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (f t)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : (Nat -> Nat) -> SProp

Arguments Prosa_Util_UnitGrowth_unit_growth_function f%_function_scope
```
