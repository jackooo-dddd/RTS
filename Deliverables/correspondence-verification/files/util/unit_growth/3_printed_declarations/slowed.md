# `slowed`

- Kind (Rocq): Fixpoint
- Rocq: `prosa.util.unit_growth.slowed`
- Lean: `Prosa.Util.UnitGrowth.slowed`
- Certificate: `ug_slowed_correspondence`

## Official Rocq

```coq
slowed : (nat -> nat) -> nat -> nat

slowed is not universe polymorphic
Arguments slowed F%function_scope n%nat_scope
slowed is transparent
Expands to: Constant prosa.util.unit_growth.slowed
Declared in library prosa.util.unit_growth, line 187, characters 0-131
slowed
     : (nat -> nat) -> nat -> nat
```

Body:

```coq
slowed =
fix slowed (F : nat -> nat) (n : nat) {struct n} : nat :=
  match n with
  | 0 => F 0
  | n'.+1 => minn (F n'.+1) (slowed F n').+1
  end
     : (nat -> nat) -> nat -> nat

Arguments slowed F%function_scope n%nat_scope
```

## Lean

```lean
Prosa.Util.UnitGrowth.slowed : (ℕ → ℕ) → ℕ → ℕ
```

Body:

```lean
def Prosa.Util.UnitGrowth.slowed : (ℕ → ℕ) → ℕ → ℕ :=
fun F x => Nat.brecOn x (Prosa.Util.UnitGrowth.slowed._f F)
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_slowed
     : (Nat -> Nat) -> Nat -> Nat
```

Body:

```coq
Prosa_Util_UnitGrowth_slowed@{} =
fun (F : Nat -> Nat) (x____at___Prosa_Util_UnitGrowth1190789944__hygCtx__hyg8 : Nat) =>
Nat_brecOn (fun _ : Nat => Nat) x____at___Prosa_Util_UnitGrowth1190789944__hygCtx__hyg8
  (Prosa_Util_UnitGrowth_slowed__f F)
     : (Nat -> Nat) -> Nat -> Nat

Arguments Prosa_Util_UnitGrowth_slowed F%_function_scope n%_Nat_scope
```
