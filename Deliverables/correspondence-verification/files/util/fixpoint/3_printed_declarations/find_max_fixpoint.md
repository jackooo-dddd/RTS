# `find_max_fixpoint`

- Kind (Rocq): Definition
- Rocq: `prosa.util.fixpoint.find_max_fixpoint`
- Lean: `Prosa.Util.Fixpoint.find_max_fixpoint`
- Certificate: `fixpoint_max_wrapper_correspondence`

## Official Rocq

```coq
find_max_fixpoint : nat -> pred nat -> (nat -> nat -> nat) -> nat -> option nat

find_max_fixpoint is not universe polymorphic
Arguments find_max_fixpoint L%nat_scope P f%function_scope h%nat_scope
find_max_fixpoint is transparent
Expands to: Constant prosa.util.fixpoint.find_max_fixpoint
Declared in library prosa.util.fixpoint, line 282, characters 13-30
find_max_fixpoint
     : nat -> pred nat -> (nat -> nat -> nat) -> nat -> option nat
```

Body:

```coq
find_max_fixpoint =
fun (L : nat) (P : pred nat) =>
let sp := [seq s <- iota 0 L | P s] in
fun (f : nat -> nat -> nat) (h : nat) =>
if @has nat P (iota 0 L) then find_max_fixpoint_of_seq f sp h else @None nat
     : nat -> pred nat -> (nat -> nat -> nat) -> nat -> option nat

Arguments find_max_fixpoint L%nat_scope P f%function_scope h%nat_scope
```

## Lean

```lean
Prosa.Util.Fixpoint.find_max_fixpoint : ℕ → (ℕ → Bool) → (ℕ → ℕ → ℕ) → ℕ → Option ℕ
```

Body:

```lean
def Prosa.Util.Fixpoint.find_max_fixpoint : ℕ → (ℕ → Bool) → (ℕ → ℕ → ℕ) → ℕ → Option ℕ :=
fun L P f h =>
  have sp := List.filter (fun s => P s) (List.range L);
  if (List.range L).any P = true then Prosa.Util.Fixpoint.find_max_fixpoint_of_seq f sp h else none
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_find_max_fixpoint
     : Nat -> (Nat -> Bool) -> (Nat -> Nat -> Nat) -> Nat -> Option_inst1 Nat
```

Body:

```coq
Prosa_Util_Fixpoint_find_max_fixpoint@{} =
fun (L : Nat) (P : Nat -> Bool) (f : Nat -> Nat -> Nat) (h : Nat) =>
let sp :=
  List_filter_inst1 Nat
    (fun n____at___Init_Prelude2408276647__hygCtx__hyg91 : Nat =>
     P n____at___Init_Prelude2408276647__hygCtx__hyg91)
    (List_range L)
  in
ite (Option_inst1 Nat) (@eq Bool (List_any_inst1 Nat (List_range L) P) Bool_true)
  (instDecidableEqBool (List_any_inst1 Nat (List_range L) P) Bool_true)
  (Prosa_Util_Fixpoint_find_max_fixpoint_of_seq f sp h) (Option_none_inst1 Nat)
     : Nat -> (Nat -> Bool) -> (Nat -> Nat -> Nat) -> Nat -> Option_inst1 Nat

Arguments Prosa_Util_Fixpoint_find_max_fixpoint L%_Nat_scope (P f)%_function_scope x%_Nat_scope
```
