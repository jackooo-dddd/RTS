# `superadditive_at`

- Kind (Rocq): Definition
- Rocq: `prosa.util.superadditivity.superadditive_at`
- Lean: `Prosa.Util.Superadditivity.superadditive_at`
- Certificate: `superadditive_at_correspondence`

## Official Rocq

```coq
superadditive_at : (nat -> nat) -> nat -> Prop

superadditive_at is not universe polymorphic
Arguments superadditive_at f%function_scope h%nat_scope
superadditive_at is transparent
Expands to: Constant prosa.util.superadditivity.superadditive_at
Declared in library prosa.util.superadditivity, line 12, characters 11-27
superadditive_at
     : (nat -> nat) -> nat -> Prop
```

Body:

```coq
superadditive_at =
fun (f : nat -> nat) (h : nat) => forall a b : nat, a + b = h -> is_true (f a + f b <= f h)
     : (nat -> nat) -> nat -> Prop

Arguments superadditive_at f%function_scope h%nat_scope
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive_at : (ℕ → ℕ) → ℕ → Prop
```

Body:

```lean
def Prosa.Util.Superadditivity.superadditive_at : (ℕ → ℕ) → ℕ → Prop :=
fun f h => ∀ (a b : ℕ), a + b = h → f a + f b ≤ f h
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive_at
     : (Nat -> Nat) -> Nat -> SProp
```

Body:

```coq
Prosa_Util_Superadditivity_superadditive_at@{} =
fun (f : Nat -> Nat) (h : Nat) =>
forall a b : Nat,
@eq Nat (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) a b) h ->
LE_le_inst1 Nat instLENat (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (f a) (f b)) (f h)
     : (Nat -> Nat) -> Nat -> SProp

Arguments Prosa_Util_Superadditivity_superadditive_at f%_function_scope a____at____internal__hyg0%_Nat_scope
```
