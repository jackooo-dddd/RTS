# `superadditive_until`

- Kind (Rocq): Definition
- Rocq: `prosa.util.superadditivity.superadditive_until`
- Lean: `Prosa.Util.Superadditivity.superadditive_until`
- Certificate: `superadditive_until_correspondence`

## Official Rocq

```coq
superadditive_until : (nat -> nat) -> nat -> Prop

superadditive_until is not universe polymorphic
Arguments superadditive_until f%function_scope h%nat_scope
superadditive_until is transparent
Expands to: Constant prosa.util.superadditivity.superadditive_until
Declared in library prosa.util.superadditivity, line 19, characters 11-30
superadditive_until
     : (nat -> nat) -> nat -> Prop
```

Body:

```coq
superadditive_until =
fun (f : nat -> nat) (h : nat) => forall x : nat, is_true (x < h) -> superadditive_at f x
     : (nat -> nat) -> nat -> Prop

Arguments superadditive_until f%function_scope h%nat_scope
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive_until : (ℕ → ℕ) → ℕ → Prop
```

Body:

```lean
def Prosa.Util.Superadditivity.superadditive_until : (ℕ → ℕ) → ℕ → Prop :=
fun f h => ∀ x < h, Prosa.Util.Superadditivity.superadditive_at f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive_until
     : (Nat -> Nat) -> Nat -> SProp
```

Body:

```coq
Prosa_Util_Superadditivity_superadditive_until@{} =
fun (f : Nat -> Nat) (h : Nat) =>
forall x : Nat, LT_lt_inst1 Nat instLTNat x h -> Prosa_Util_Superadditivity_superadditive_at f x
     : (Nat -> Nat) -> Nat -> SProp

Arguments Prosa_Util_Superadditivity_superadditive_until f%_function_scope
  a____at____internal__hyg0%_Nat_scope
```
