# `first0`

- Kind (Rocq): Definition
- Rocq: `prosa.util.list.first0`
- Lean: `Prosa.Util.List.first0`
- Certificate: `first0_definition_certificate`

## Official Rocq

```coq
first0 : seq nat -> nat

first0 is not universe polymorphic
Arguments first0 s%seq_scope
first0 is transparent
Expands to: Constant prosa.util.list.first0
Declared in library prosa.util.list, line 12, characters 11-17
first0
     : seq nat -> nat
```

Body:

```coq
first0 = @head nat 0
     : seq nat -> nat

Arguments first0 s%seq_scope
```

## Lean

```lean
Prosa.Util.List.first0 : List ℕ → ℕ
```

Body:

```lean
def Prosa.Util.List.first0 : List ℕ → ℕ :=
fun xs => xs.headD 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_first0
     : ImportedListSimple.List_inst1 Nat -> Nat
```

Body:

```coq
Prosa_Util_List_first0@{} =
fun xs : ImportedListSimple.List_inst1 Nat =>
List_headD_inst1 Nat xs (ImportedListSimple.OfNat_ofNat_inst1 Nat 0 (ImportedListSimple.instOfNatNat 0))
     : ImportedListSimple.List_inst1 Nat -> Nat

Arguments Prosa_Util_List_first0 xs
```
