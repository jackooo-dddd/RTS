# `subadditive_until`

- Kind (Rocq): Definition
- Rocq: `prosa.util.subadditivity.subadditive_until`
- Lean: `Prosa.Util.Subadditivity.subadditive_until`
- Certificate: `subadditive_until_correspondence_certificate`

## Official Rocq

```coq
subadditive_until : (nat -> nat) -> nat -> Prop

subadditive_until is not universe polymorphic
Arguments subadditive_until f%function_scope h%nat_scope
subadditive_until is transparent
Expands to: Constant prosa.util.subadditivity.subadditive_until
Declared in library prosa.util.subadditivity, line 18, characters 11-28
subadditive_until
     : (nat -> nat) -> nat -> Prop
```

Body:

```coq
subadditive_until =
fun (f : nat -> nat) (h : nat) => forall x : nat, is_true (x < h) -> subadditive_at f x
     : (nat -> nat) -> nat -> Prop

Arguments subadditive_until f%function_scope h%nat_scope
```

## Lean

```lean
Prosa.Util.Subadditivity.subadditive_until : (ℕ → ℕ) → ℕ → Prop
```

Body:

```lean
def Prosa.Util.Subadditivity.subadditive_until : (ℕ → ℕ) → ℕ → Prop :=
fun f h => ∀ x < h, Prosa.Util.Subadditivity.subadditive_at f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Subadditivity_subadditive_until
     : (Nat -> Nat) -> Nat -> SProp
```

Body:

```coq
Prosa_Util_Subadditivity_subadditive_until@{} =
fun (f : Nat -> Nat) (h : Nat) =>
forall x : Nat, LT_lt_inst1 Nat instLTNat x h -> Prosa_Util_Subadditivity_subadditive_at f x
     : (Nat -> Nat) -> Nat -> SProp

Arguments Prosa_Util_Subadditivity_subadditive_until f%_function_scope a____at____internal__hyg0%_Nat_scope
```
