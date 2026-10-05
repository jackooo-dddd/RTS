# `leqRW`

- Kind (Rocq): Definition
- Rocq: `prosa.util.setoid.leqRW`
- Lean: `Prosa.Util.Setoid.leqRW`
- Certificate: `leqRW_definition_type_certificate`

## Official Rocq

```coq
leqRW : forall {m n : nat}, is_true (m <= n) -> (m <= n)%coq_nat

leqRW is not universe polymorphic
Arguments leqRW {m n}%nat_scope _
leqRW is transparent
Expands to: Constant prosa.util.setoid.leqRW
Declared in library prosa.util.setoid, line 57, characters 11-16
@leqRW
     : forall m n : nat, is_true (m <= n) -> (m <= n)%coq_nat
```

Body:

```coq
leqRW =
fun m n : nat => @elimT (m <= n)%coq_nat (m <= n) (@leP m n)
     : forall {m n : nat}, is_true (m <= n) -> (m <= n)%coq_nat

Arguments leqRW {m n}%nat_scope _
```

## Lean

```lean
@Prosa.Util.Setoid.leqRW : ∀ {m n : ℕ}, m ≤ n → m ≤ n
```

Body:

```lean
def Prosa.Util.Setoid.leqRW : ∀ {m n : ℕ}, m ≤ n → m ≤ n :=
fun {m n} h => h
```

## Lean, imported into Rocq

```coq
Prosa_Util_Setoid_leqRW
     : forall m n : Nat, LE_le_inst1 Nat instLENat m n -> LE_le_inst1 Nat instLENat m n
```

Body:

```coq
Prosa_Util_Setoid_leqRW@{} =
fun (m n : Nat) (h : LE_le_inst1 Nat instLENat m n) => h
     : forall m n : Nat, LE_le_inst1 Nat instLENat m n -> LE_le_inst1 Nat instLENat m n

Arguments Prosa_Util_Setoid_leqRW (m n)%_Nat_scope h
```
