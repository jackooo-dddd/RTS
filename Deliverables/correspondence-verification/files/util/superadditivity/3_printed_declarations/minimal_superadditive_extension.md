# `minimal_superadditive_extension`

- Kind (Rocq): Definition
- Rocq: `prosa.util.superadditivity.minimal_superadditive_extension`
- Lean: `Prosa.Util.Superadditivity.minimal_superadditive_extension`
- Certificate: `sa_minimal_extension_related`

## Official Rocq

```coq
minimal_superadditive_extension : (nat -> nat) -> nat -> nat

minimal_superadditive_extension is not universe polymorphic
Arguments minimal_superadditive_extension f%function_scope h%nat_scope
minimal_superadditive_extension is transparent
Expands to: Constant prosa.util.superadditivity.minimal_superadditive_extension
Declared in library prosa.util.superadditivity, line 150, characters 15-46
minimal_superadditive_extension
     : (nat -> nat) -> nat -> nat
```

Body:

```coq
minimal_superadditive_extension =
fun (f : nat -> nat) (h : nat) => max0 [seq f a + f (h - a) | a <- index_iota 1 h]
     : (nat -> nat) -> nat -> nat

Arguments minimal_superadditive_extension f%function_scope h%nat_scope
```

## Lean

```lean
Prosa.Util.Superadditivity.minimal_superadditive_extension : (ℕ → ℕ) → ℕ → ℕ
```

Body:

```lean
def Prosa.Util.Superadditivity.minimal_superadditive_extension : (ℕ → ℕ) → ℕ → ℕ :=
fun f h => Prosa.Util.List.max0 (List.map (fun a => f a + f (h - a)) (Prosa.Util.List.index_iota 1 h))
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_minimal_superadditive_extension
     : (Nat -> Nat) -> Nat -> Nat
```

Body:

```coq
Prosa_Util_Superadditivity_minimal_superadditive_extension@{} =
fun (f : Nat -> Nat) (h : Nat) =>
Prosa_Util_List_max0
  (List_map_inst3 Nat Nat
     (fun a : Nat =>
      HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (f a)
        (f (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) h a)))
     (Prosa_Util_List_index_iota (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) h))
     : (Nat -> Nat) -> Nat -> Nat

Arguments Prosa_Util_Superadditivity_minimal_superadditive_extension f%_function_scope n%_Nat_scope
```
