# `shift_points_neg`

- Kind (Rocq): Definition
- Rocq: `prosa.util.list.shift_points_neg`
- Lean: `Prosa.Util.List.shift_points_neg`
- Certificate: `shift_points_neg_definition_certificate`

## Official Rocq

```coq
shift_points_neg : seq nat -> nat -> seq nat

shift_points_neg is not universe polymorphic
Arguments shift_points_neg xs%seq_scope s%nat_scope
shift_points_neg is transparent
Expands to: Constant prosa.util.list.shift_points_neg
Declared in library prosa.util.list, line 888, characters 11-27
shift_points_neg
     : seq nat -> nat -> seq nat
```

Body:

```coq
shift_points_neg =
fun (xs : seq nat) (s : nat) => let nonsmall := [seq x <- xs | s <= x] in [seq x - s | x <- nonsmall]
     : seq nat -> nat -> seq nat

Arguments shift_points_neg xs%seq_scope s%nat_scope
```

## Lean

```lean
Prosa.Util.List.shift_points_neg : List ℕ → ℕ → List ℕ
```

Body:

```lean
def Prosa.Util.List.shift_points_neg : List ℕ → ℕ → List ℕ :=
fun xs s => List.map (fun x => x - s) (List.filter (fun x => decide (s ≤ x)) xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_shift_points_neg
     : List_inst1 Nat -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Util_List_shift_points_neg@{} =
fun (xs : List_inst1 Nat) (s : Nat) =>
List_map_inst3 Nat Nat (fun x : Nat => HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) x s)
  (List_filter_inst1 Nat (fun x : Nat => Decidable_decide (LE_le_inst1 Nat instLENat s x) (Nat_decLe s x)) xs)
     : List_inst1 Nat -> Nat -> List_inst1 Nat

Arguments Prosa_Util_List_shift_points_neg xs
  x____at___Init_Data_List_Basic527151790__hygCtx__hyg16%_Nat_scope
```
