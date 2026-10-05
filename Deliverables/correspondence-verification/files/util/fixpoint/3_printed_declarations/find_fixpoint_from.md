# `find_fixpoint_from`

- Kind (Rocq): Fixpoint
- Rocq: `prosa.util.fixpoint.find_fixpoint_from`
- Lean: `Prosa.Util.Fixpoint.find_fixpoint_from`
- Certificate: `fixpoint_from_correspondence`

## Official Rocq

```coq
find_fixpoint_from : (nat -> nat) -> nat -> nat -> nat -> option nat

find_fixpoint_from is not universe polymorphic
Arguments find_fixpoint_from f%function_scope (x h fuel)%nat_scope
find_fixpoint_from is transparent
Expands to: Constant prosa.util.fixpoint.find_fixpoint_from
Declared in library prosa.util.fixpoint, line 16, characters 0-253
find_fixpoint_from
     : (nat -> nat) -> nat -> nat -> nat -> option nat
```

Body:

```coq
find_fixpoint_from =
fix find_fixpoint_from (f : nat -> nat) (x h fuel : nat) {struct fuel} : option nat :=
  match fuel with
  | 0 => @None nat
  | fuel'.+1 =>
      if f x == x then @Some nat x else if f x <= h then find_fixpoint_from f (f x) h fuel' else @None nat
  end
     : (nat -> nat) -> nat -> nat -> nat -> option nat

Arguments find_fixpoint_from f%function_scope (x h fuel)%nat_scope
```

## Lean

```lean
Prosa.Util.Fixpoint.find_fixpoint_from : (ℕ → ℕ) → ℕ → ℕ → ℕ → Option ℕ
```

Body:

```lean
def Prosa.Util.Fixpoint.find_fixpoint_from : (ℕ → ℕ) → ℕ → ℕ → ℕ → Option ℕ :=
fun f x h x_1 => Nat.brecOn (motive := fun x => ℕ → Option ℕ) x_1 (Prosa.Util.Fixpoint.find_fixpoint_from._f f h) x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_find_fixpoint_from
     : (Nat -> Nat) -> Nat -> Nat -> Nat -> Option_inst1 Nat
```

Body:

```coq
Prosa_Util_Fixpoint_find_fixpoint_from@{} =
fun (f : Nat -> Nat) (x h x____at___Prosa_Util_Fixpoint2380743835__hygCtx__hyg11 : Nat) =>
Nat_brecOn (fun _ : Nat => Nat -> Option_inst1 Nat) x____at___Prosa_Util_Fixpoint2380743835__hygCtx__hyg11
  (Prosa_Util_Fixpoint_find_fixpoint_from__f f h) x
     : (Nat -> Nat) -> Nat -> Nat -> Nat -> Option_inst1 Nat

Arguments Prosa_Util_Fixpoint_find_fixpoint_from f%_function_scope (x h x)%_Nat_scope
```
