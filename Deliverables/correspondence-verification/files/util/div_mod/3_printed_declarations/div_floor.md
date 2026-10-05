# `div_floor`

- Kind (Rocq): Definition
- Rocq: `prosa.util.div_mod.div_floor`
- Lean: `Prosa.Util.Div_mod.div_floor`
- Certificate: `div_floor_definition_certificate`

## Official Rocq

```coq
div_floor : nat -> nat -> nat

div_floor is not universe polymorphic
Arguments div_floor (x y)%nat_scope
div_floor is transparent
Expands to: Constant prosa.util.div_mod.div_floor
Declared in library prosa.util.div_mod, line 105, characters 11-20
div_floor
     : nat -> nat -> nat
```

Body:

```coq
div_floor = fun x : nat => [eta divn x]
     : nat -> nat -> nat

Arguments div_floor (x y)%nat_scope
```

## Lean

```lean
Prosa.Util.Div_mod.div_floor : ℕ → ℕ → ℕ
```

Body:

```lean
def Prosa.Util.Div_mod.div_floor : ℕ → ℕ → ℕ :=
fun x y => x / y
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_div_floor
     : Nat -> Nat -> Nat
```

Body:

```coq
Prosa_Util_Div_mod_div_floor@{} =
fun x y : Nat => HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) x y
     : Nat -> Nat -> Nat

Arguments Prosa_Util_Div_mod_div_floor (x n)%_Nat_scope
```
