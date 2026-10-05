# `last0`

- Kind (Rocq): Definition
- Rocq: `prosa.util.list.last0`
- Lean: `Prosa.Util.List.last0`
- Certificate: `last0_definition_certificate`

## Official Rocq

```coq
last0 : seq nat -> nat

last0 is not universe polymorphic
Arguments last0 s%seq_scope
last0 is transparent
Expands to: Constant prosa.util.list.last0
Declared in library prosa.util.list, line 13, characters 11-16
last0
     : seq nat -> nat
```

Body:

```coq
last0 = @last nat 0
     : seq nat -> nat

Arguments last0 s%seq_scope
```

## Lean

```lean
Prosa.Util.List.last0 : List ℕ → ℕ
```

Body:

```lean
def Prosa.Util.List.last0 : List ℕ → ℕ :=
fun xs => xs.getLastD 0
```

## Lean, imported into Rocq

```coq
ImportedListSimple.Prosa_Util_List_last0
     : ImportedListSimple.List_inst1 Nat -> Nat
```

Body:

```coq
ImportedListSimple.Prosa_Util_List_last0@{} =
fun xs : ImportedListSimple.List_inst1 Nat =>
ImportedListSimple.List_getLastD_inst1 Nat xs
  (ImportedListSimple.OfNat_ofNat_inst1 Nat 0 (ImportedListSimple.instOfNatNat 0))
     : ImportedListSimple.List_inst1 Nat -> Nat

Arguments ImportedListSimple.Prosa_Util_List_last0 xs
```
