# `find_fixpoint`

- Kind (Rocq): Definition
- Rocq: `prosa.util.fixpoint.find_fixpoint`
- Lean: `Prosa.Util.Fixpoint.find_fixpoint`
- Certificate: `fixpoint_correspondence`

## Official Rocq

```coq
find_fixpoint : (nat -> nat) -> nat -> option nat

find_fixpoint is not universe polymorphic
Arguments find_fixpoint f%function_scope h%nat_scope
find_fixpoint is transparent
Expands to: Constant prosa.util.fixpoint.find_fixpoint
Declared in library prosa.util.fixpoint, line 28, characters 11-24
find_fixpoint
     : (nat -> nat) -> nat -> option nat
```

Body:

```coq
find_fixpoint =
fun (f : nat -> nat) (h : nat) => find_fixpoint_from f 1 h h
     : (nat -> nat) -> nat -> option nat

Arguments find_fixpoint f%function_scope h%nat_scope
```

## Lean

```lean
Prosa.Util.Fixpoint.find_fixpoint : (ℕ → ℕ) → ℕ → Option ℕ
```

Body:

```lean
def Prosa.Util.Fixpoint.find_fixpoint : (ℕ → ℕ) → ℕ → Option ℕ :=
fun f h => Prosa.Util.Fixpoint.find_fixpoint_from f 1 h h
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_find_fixpoint
     : (Nat -> Nat) -> Nat -> Option_inst1 Nat
```

Body:

```coq
Prosa_Util_Fixpoint_find_fixpoint@{} =
fun (f : Nat -> Nat) (h : Nat) =>
Prosa_Util_Fixpoint_find_fixpoint_from f (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) h h
     : (Nat -> Nat) -> Nat -> Option_inst1 Nat

Arguments Prosa_Util_Fixpoint_find_fixpoint f%_function_scope x%_Nat_scope
```
