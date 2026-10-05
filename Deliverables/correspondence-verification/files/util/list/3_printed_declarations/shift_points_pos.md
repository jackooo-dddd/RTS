# `shift_points_pos`

- Kind (Rocq): Definition
- Rocq: `prosa.util.list.shift_points_pos`
- Lean: `Prosa.Util.List.shift_points_pos`
- Certificate: `shift_points_pos_definition_certificate`

## Official Rocq

```coq
shift_points_pos : seq nat -> nat -> seq nat

shift_points_pos is not universe polymorphic
Arguments shift_points_pos xs%seq_scope s%nat_scope
shift_points_pos is transparent
Expands to: Constant prosa.util.list.shift_points_pos
Declared in library prosa.util.list, line 886, characters 11-27
shift_points_pos
     : seq nat -> nat -> seq nat
```

Body:

```coq
shift_points_pos = fun (xs : seq nat) (s : nat) => [seq s + i | i <- xs]
     : seq nat -> nat -> seq nat

Arguments shift_points_pos xs%seq_scope s%nat_scope
```

## Lean

```lean
Prosa.Util.List.shift_points_pos : List ℕ → ℕ → List ℕ
```

Body:

```lean
def Prosa.Util.List.shift_points_pos : List ℕ → ℕ → List ℕ :=
fun xs s => List.map (fun x => s + x) xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_shift_points_pos
     : List_inst1 Nat -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Util_List_shift_points_pos@{} =
fun (xs : List_inst1 Nat) (s : Nat) =>
List_map_inst3 Nat Nat (fun x : Nat => HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) s x) xs
     : List_inst1 Nat -> Nat -> List_inst1 Nat

Arguments Prosa_Util_List_shift_points_pos xs
  x____at___Init_Data_List_Basic527151790__hygCtx__hyg16%_Nat_scope
```
