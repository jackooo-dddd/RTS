# `subadditive_standard`

- Kind (Rocq): Definition
- Rocq: `prosa.util.subadditivity.subadditive_standard`
- Lean: `Prosa.Util.Subadditivity.subadditive_standard`
- Certificate: `subadditive_standard_correspondence_certificate`

## Official Rocq

```coq
subadditive_standard : (nat -> nat) -> Prop

subadditive_standard is not universe polymorphic
Arguments subadditive_standard f%function_scope
subadditive_standard is transparent
Expands to: Constant prosa.util.subadditivity.subadditive_standard
Declared in library prosa.util.subadditivity, line 33, characters 11-31
subadditive_standard
     : (nat -> nat) -> Prop
```

Body:

```coq
subadditive_standard =
fun f : nat -> nat => forall a b : nat, is_true (f (a + b) <= f a + f b)
     : (nat -> nat) -> Prop

Arguments subadditive_standard f%function_scope
```

## Lean

```lean
Prosa.Util.Subadditivity.subadditive_standard : (ℕ → ℕ) → Prop
```

Body:

```lean
def Prosa.Util.Subadditivity.subadditive_standard : (ℕ → ℕ) → Prop :=
fun f => ∀ (a b : ℕ), f (a + b) ≤ f a + f b
```

## Lean, imported into Rocq

```coq
Prosa_Util_Subadditivity_subadditive_standard
     : (Nat -> Nat) -> SProp
```

Body:

```coq
Prosa_Util_Subadditivity_subadditive_standard@{} =
fun f : Nat -> Nat =>
forall a b : Nat,
LE_le_inst1 Nat instLENat (f (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) a b))
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (f a) (f b))
     : (Nat -> Nat) -> SProp

Arguments Prosa_Util_Subadditivity_subadditive_standard f%_function_scope
```
