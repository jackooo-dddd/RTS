# `subadditive_at`

- Kind (Rocq): Definition
- Rocq: `prosa.util.subadditivity.subadditive_at`
- Lean: `Prosa.Util.Subadditivity.subadditive_at`
- Certificate: `subadditive_at_correspondence_certificate`

## Official Rocq

```coq
subadditive_at : (nat -> nat) -> nat -> Prop

subadditive_at is not universe polymorphic
Arguments subadditive_at f%function_scope h%nat_scope
subadditive_at is transparent
Expands to: Constant prosa.util.subadditivity.subadditive_at
Declared in library prosa.util.subadditivity, line 11, characters 11-25
subadditive_at
     : (nat -> nat) -> nat -> Prop
```

Body:

```coq
subadditive_at =
fun (f : nat -> nat) (h : nat) => forall a b : nat, a + b = h -> is_true (f h <= f a + f b)
     : (nat -> nat) -> nat -> Prop

Arguments subadditive_at f%function_scope h%nat_scope
```

## Lean

```lean
Prosa.Util.Subadditivity.subadditive_at : (ℕ → ℕ) → ℕ → Prop
```

Body:

```lean
def Prosa.Util.Subadditivity.subadditive_at : (ℕ → ℕ) → ℕ → Prop :=
fun f h => ∀ (a b : ℕ), a + b = h → f h ≤ f a + f b
```

## Lean, imported into Rocq

```coq
Prosa_Util_Subadditivity_subadditive_at
     : (Nat -> Nat) -> Nat -> SProp
```

Body:

```coq
Prosa_Util_Subadditivity_subadditive_at@{} =
fun (f : Nat -> Nat) (h : Nat) =>
forall a b : Nat,
@eq Nat (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) a b) h ->
LE_le_inst1 Nat instLENat (f h) (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (f a) (f b))
     : (Nat -> Nat) -> Nat -> SProp

Arguments Prosa_Util_Subadditivity_subadditive_at f%_function_scope a____at____internal__hyg0%_Nat_scope
```
