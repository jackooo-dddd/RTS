# `distances`

- Kind (Rocq): Definition
- Rocq: `prosa.util.nondecreasing.distances`
- Lean: `Prosa.Util.Nondecreasing.distances`
- Certificate: `distances_definition_certificate`

## Official Rocq

```coq
distances : seq nat -> seq nat

distances is not universe polymorphic
Arguments distances xs%seq_scope
distances is transparent
Expands to: Constant prosa.util.nondecreasing.distances
Declared in library prosa.util.nondecreasing, line 33, characters 13-22
distances
     : seq nat -> seq nat
```

Body:

```coq
distances =
fun xs : seq nat => [seq x2 - x1 | '(x1, x2) <- @zip nat nat xs (@drop nat 1 xs)]
     : seq nat -> seq nat

Arguments distances xs%seq_scope
```

## Lean

```lean
Prosa.Util.Nondecreasing.distances : List ℕ → List ℕ
```

Body:

```lean
def Prosa.Util.Nondecreasing.distances : List ℕ → List ℕ :=
fun xs => List.map (fun p => p.2 - p.1) (xs.zip (List.drop 1 xs))
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_distances
     : List_inst1 Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Util_Nondecreasing_distances@{} =
fun xs : List_inst1 Nat =>
List_map_inst3 (Prod_inst3 Nat Nat) Nat (fun p : Prod_inst3 Nat Nat => Nat_sub (snd8 _ _ p) (fst8 _ _ p))
  (List_zipWith_inst7 Nat Nat (Prod_inst3 Nat Nat) (Prod_mk_inst3 Nat Nat) xs (List_drop_inst1 Nat 1 xs))
     : List_inst1 Nat -> List_inst1 Nat

Arguments Prosa_Util_Nondecreasing_distances xs
```
