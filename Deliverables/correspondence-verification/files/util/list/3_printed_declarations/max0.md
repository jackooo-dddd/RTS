# `max0`

- Kind (Rocq): Definition
- Rocq: `prosa.util.list.max0`
- Lean: `Prosa.Util.List.max0`
- Certificate: `max0_definition_certificate`

## Official Rocq

```coq
max0 : seq nat -> nat

max0 is not universe polymorphic
Arguments max0 s%seq_scope
max0 is transparent
Expands to: Constant prosa.util.list.max0
Declared in library prosa.util.list, line 11, characters 11-15
max0
     : seq nat -> nat
```

Body:

```coq
max0 = @foldl nat nat maxn 0
     : seq nat -> nat

Arguments max0 s%seq_scope
```

## Lean

```lean
Prosa.Util.List.max0 : List ℕ → ℕ
```

Body:

```lean
def Prosa.Util.List.max0 : List ℕ → ℕ :=
fun xs => List.foldl Nat.max 0 xs
```

## Lean, imported into Rocq

```coq
ImportedListSimple.Prosa_Util_List_max0
     : ImportedListSimple.List_inst1 Nat -> Nat
```

Body:

```coq
ImportedListSimple.Prosa_Util_List_max0@{} =
fun xs : ImportedListSimple.List_inst1 Nat =>
ImportedListSimple.List_foldl_inst3 Nat Nat ImportedListSimple.Nat_max
  (ImportedListSimple.OfNat_ofNat_inst1 Nat 0 (ImportedListSimple.instOfNatNat 0)) xs
     : ImportedListSimple.List_inst1 Nat -> Nat

Arguments ImportedListSimple.Prosa_Util_List_max0 xs
```
