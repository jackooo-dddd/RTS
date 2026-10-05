# `unit_growth_function_k_steps_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.unit_growth.unit_growth_function_k_steps_bounded`
- Lean: `Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded`
- Certificate: `unit_growth_function_k_steps_bounded_statement_certificate`

## Official Rocq

```coq
unit_growth_function_k_steps_bounded :
forall f : nat -> nat, unit_growth_function f -> forall x k : nat, is_true (f (x + k) <= k + f x)

unit_growth_function_k_steps_bounded is not universe polymorphic
Arguments unit_growth_function_k_steps_bounded f%function_scope H_unit_growth_function (x k)%nat_scope
unit_growth_function_k_steps_bounded is opaque
Expands to: Constant prosa.util.unit_growth.unit_growth_function_k_steps_bounded
Declared in library prosa.util.unit_growth, line 19, characters 8-44
unit_growth_function_k_steps_bounded
     : forall f : nat -> nat, unit_growth_function f -> forall x k : nat, is_true (f (x + k) <= k + f x)
```

## Lean

```lean
Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded : ∀ (f : ℕ → ℕ),
  Prosa.Util.UnitGrowth.unit_growth_function f → ∀ (x k : ℕ), f (x + k) ≤ k + f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_unit_growth_function_k_steps_bounded
     : forall f : Nat -> Nat,
       Prosa_Util_UnitGrowth_unit_growth_function f ->
       forall x k : Nat,
       LE_le_inst1 Nat instLENat (f (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) x k))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) k (f x))
```
