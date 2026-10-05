# `superadditive_standard`

- Kind (Rocq): Definition
- Rocq: `prosa.util.superadditivity.superadditive_standard`
- Lean: `Prosa.Util.Superadditivity.superadditive_standard`
- Certificate: `superadditive_standard_correspondence`

## Official Rocq

```coq
superadditive_standard : (nat -> nat) -> Prop

superadditive_standard is not universe polymorphic
Arguments superadditive_standard f%function_scope
superadditive_standard is transparent
Expands to: Constant prosa.util.superadditivity.superadditive_standard
Declared in library prosa.util.superadditivity, line 34, characters 11-33
superadditive_standard
     : (nat -> nat) -> Prop
```

Body:

```coq
superadditive_standard =
fun f : nat -> nat => forall a b : nat, is_true (f a + f b <= f (a + b))
     : (nat -> nat) -> Prop

Arguments superadditive_standard f%function_scope
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive_standard : (ℕ → ℕ) → Prop
```

Body:

```lean
def Prosa.Util.Superadditivity.superadditive_standard : (ℕ → ℕ) → Prop :=
fun f => ∀ (a b : ℕ), f a + f b ≤ f (a + b)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive_standard
     : (Nat -> Nat) -> SProp
```

Body:

```coq
Prosa_Util_Superadditivity_superadditive_standard@{} =
fun f : Nat -> Nat =>
forall a b : Nat,
LE_le_inst1 Nat instLENat (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (f a) (f b))
  (f (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) a b))
     : (Nat -> Nat) -> SProp

Arguments Prosa_Util_Superadditivity_superadditive_standard f%_function_scope
```
