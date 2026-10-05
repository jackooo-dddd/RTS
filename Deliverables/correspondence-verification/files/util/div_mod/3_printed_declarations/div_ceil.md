# `div_ceil`

- Kind (Rocq): Definition
- Rocq: `prosa.util.div_mod.div_ceil`
- Lean: `Prosa.Util.Div_mod.div_ceil`
- Certificate: `div_ceil_definition_certificate`

## Official Rocq

```coq
div_ceil : nat -> nat -> nat

div_ceil is not universe polymorphic
Arguments div_ceil (x y)%nat_scope
div_ceil is transparent
Expands to: Constant prosa.util.div_mod.div_ceil
Declared in library prosa.util.div_mod, line 106, characters 11-19
div_ceil
     : nat -> nat -> nat
```

Body:

```coq
div_ceil = fun x y : nat => if y %| x then x %/ y else (x %/ y).+1
     : nat -> nat -> nat

Arguments div_ceil (x y)%nat_scope
```

## Lean

```lean
Prosa.Util.Div_mod.div_ceil : ℕ → ℕ → ℕ
```

Body:

```lean
def Prosa.Util.Div_mod.div_ceil : ℕ → ℕ → ℕ :=
fun x y => if y ∣ x then x / y else x / y + 1
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_div_ceil
     : Nat -> Nat -> Nat
```

Body:

```coq
Prosa_Util_Div_mod_div_ceil@{} =
fun x y : Nat =>
ite Nat (Dvd_dvd_inst1 Nat Nat_instDvd y x) (Nat_decidable_dvd y x)
  (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) x y)
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
     (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) x y)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : Nat -> Nat -> Nat

Arguments Prosa_Util_Div_mod_div_ceil (x n)%_Nat_scope
```
