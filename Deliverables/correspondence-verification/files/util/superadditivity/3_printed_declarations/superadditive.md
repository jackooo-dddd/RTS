# `superadditive`

- Kind (Rocq): Definition
- Rocq: `prosa.util.superadditivity.superadditive`
- Lean: `Prosa.Util.Superadditivity.superadditive`
- Certificate: `superadditive_correspondence`

## Official Rocq

```coq
superadditive : (nat -> nat) -> Prop

superadditive is not universe polymorphic
Arguments superadditive f%function_scope
superadditive is transparent
Expands to: Constant prosa.util.superadditivity.superadditive
Declared in library prosa.util.superadditivity, line 26, characters 11-24
superadditive
     : (nat -> nat) -> Prop
```

Body:

```coq
superadditive = fun f : nat -> nat => forall h : nat, superadditive_at f h
     : (nat -> nat) -> Prop

Arguments superadditive f%function_scope
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive : (ℕ → ℕ) → Prop
```

Body:

```lean
def Prosa.Util.Superadditivity.superadditive : (ℕ → ℕ) → Prop :=
fun f => ∀ (h : ℕ), Prosa.Util.Superadditivity.superadditive_at f h
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive
     : (Nat -> Nat) -> SProp
```

Body:

```coq
Prosa_Util_Superadditivity_superadditive@{} =
fun f : Nat -> Nat => forall h : Nat, Prosa_Util_Superadditivity_superadditive_at f h
     : (Nat -> Nat) -> SProp

Arguments Prosa_Util_Superadditivity_superadditive f%_function_scope
```
