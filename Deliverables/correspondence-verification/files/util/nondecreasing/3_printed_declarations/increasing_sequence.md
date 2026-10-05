# `increasing_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.util.nondecreasing.increasing_sequence`
- Lean: `Prosa.Util.Nondecreasing.increasing_sequence`
- Certificate: `increasing_sequence_definition_certificate`

## Official Rocq

```coq
increasing_sequence : seq nat -> Prop

increasing_sequence is not universe polymorphic
Arguments increasing_sequence xs%seq_scope
increasing_sequence is transparent
Expands to: Constant prosa.util.nondecreasing.increasing_sequence
Declared in library prosa.util.nondecreasing, line 21, characters 13-32
increasing_sequence
     : seq nat -> Prop
```

Body:

```coq
increasing_sequence =
fun xs : seq nat =>
forall n1 n2 : nat, is_true (n1 < n2 < @size nat xs) -> is_true (@nth nat 0 xs n1 < @nth nat 0 xs n2)
     : seq nat -> Prop

Arguments increasing_sequence xs%seq_scope
```

## Lean

```lean
Prosa.Util.Nondecreasing.increasing_sequence : List ℕ → Prop
```

Body:

```lean
def Prosa.Util.Nondecreasing.increasing_sequence : List ℕ → Prop :=
fun xs =>
  ∀ (n1 n2 : ℕ), n1 < n2 ∧ n2 < xs.length → Prosa.Util.Nondecreasing.nthD✝ xs n1 < Prosa.Util.Nondecreasing.nthD✝ xs n2
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_increasing_sequence
     : List_inst1 Nat -> SProp
```

Body:

```coq
Prosa_Util_Nondecreasing_increasing_sequence@{} =
fun xs : List_inst1 Nat =>
forall n1 n2 : Nat,
And (LT_lt_inst1 Nat instLTNat n1 n2) (LT_lt_inst1 Nat instLTNat n2 (List_length_inst1 Nat xs)) ->
Nat_succ
  (Option_inst1_recl Nat (fun _ : Option_inst1 Nat => Nat) 0 (fun a : Nat => a)
     (List_get__qInternal_inst1 Nat xs n1)) <=
Option_inst1_recl Nat (fun _ : Option_inst1 Nat => Nat) 0 (fun a : Nat => a)
  (List_get__qInternal_inst1 Nat xs n2)
     : List_inst1 Nat -> SProp

Arguments Prosa_Util_Nondecreasing_increasing_sequence xs
```
