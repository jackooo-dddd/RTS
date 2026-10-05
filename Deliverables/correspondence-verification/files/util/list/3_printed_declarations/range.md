# `range`

- Kind (Rocq): Definition
- Rocq: `prosa.util.list.range`
- Lean: `Prosa.Util.List.range`
- Certificate: `range_definition_certificate`

## Official Rocq

```coq
range : nat -> nat -> seq nat

range is not universe polymorphic
Arguments range (a b)%nat_scope
range is transparent
Expands to: Constant prosa.util.list.range
Declared in library prosa.util.list, line 632, characters 11-16
range
     : nat -> nat -> seq nat
```

Body:

```coq
range = fun a b : nat => bigop.index_iota a b.+1
     : nat -> nat -> seq nat

Arguments range (a b)%nat_scope
```

## Lean

```lean
Prosa.Util.List.range : ℕ → ℕ → List ℕ
```

Body:

```lean
def Prosa.Util.List.range : ℕ → ℕ → List ℕ :=
fun a b => Prosa.Util.List.index_iota a (b + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_range
     : Nat -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Util_List_range@{} =
fun a b : Nat =>
Prosa_Util_List_index_iota a
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) b (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : Nat -> Nat -> List_inst1 Nat

Arguments Prosa_Util_List_range
  (x____at___Init_Data_List_Basic527151790__hygCtx__hyg14
   x____at___Init_Data_List_Basic527151790__hygCtx__hyg16)%_Nat_scope
```
