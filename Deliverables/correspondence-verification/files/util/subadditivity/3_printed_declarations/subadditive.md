# `subadditive`

- Kind (Rocq): Definition
- Rocq: `prosa.util.subadditivity.subadditive`
- Lean: `Prosa.Util.Subadditivity.subadditive`
- Certificate: `subadditive_correspondence_certificate`

## Official Rocq

```coq
subadditive : (nat -> nat) -> Prop

subadditive is not universe polymorphic
Arguments subadditive f%function_scope
subadditive is transparent
Expands to: Constant prosa.util.subadditivity.subadditive
Declared in library prosa.util.subadditivity, line 25, characters 11-22
subadditive
     : (nat -> nat) -> Prop
```

Body:

```coq
subadditive = fun f : nat -> nat => forall h : nat, subadditive_at f h
     : (nat -> nat) -> Prop

Arguments subadditive f%function_scope
```

## Lean

```lean
Prosa.Util.Subadditivity.subadditive : (ℕ → ℕ) → Prop
```

Body:

```lean
def Prosa.Util.Subadditivity.subadditive : (ℕ → ℕ) → Prop :=
fun f => ∀ (h : ℕ), Prosa.Util.Subadditivity.subadditive_at f h
```

## Lean, imported into Rocq

```coq
Prosa_Util_Subadditivity_subadditive
     : (Nat -> Nat) -> SProp
```

Body:

```coq
Prosa_Util_Subadditivity_subadditive@{} =
fun f : Nat -> Nat => forall h : Nat, Prosa_Util_Subadditivity_subadditive_at f h
     : (Nat -> Nat) -> SProp

Arguments Prosa_Util_Subadditivity_subadditive f%_function_scope
```
