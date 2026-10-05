# `suffix_sum`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.maximal_arrival_sequence.suffix_sum`
- Lean: `Prosa.Implementation.Definitions.MaximalArrivalSequence.suffix_sum`
- Certificate: `suffix_sum_correspondence`

## Official Rocq

```coq
suffix_sum : seq nat -> nat -> nat

suffix_sum is not universe polymorphic
Arguments suffix_sum xs%seq_scope n%nat_scope
suffix_sum is transparent
Expands to: Constant prosa.implementation.definitions.maximal_arrival_sequence.suffix_sum
Declared in library prosa.implementation.definitions.maximal_arrival_sequence, line 37, characters 15-25
suffix_sum
     : seq nat -> nat -> nat
```

Body:

```coq
suffix_sum =
fun (xs : seq nat) (n : nat) => \sum_(@size nat xs - n <= t < @size nat xs) @nth nat 0 xs t
     : seq nat -> nat -> nat

Arguments suffix_sum xs%seq_scope n%nat_scope
```

## Lean

```lean
Prosa.Implementation.Definitions.MaximalArrivalSequence.suffix_sum : List ℕ → ℕ → ℕ
```

Body:

```lean
def Prosa.Implementation.Definitions.MaximalArrivalSequence.suffix_sum : List ℕ → ℕ → ℕ :=
fun xs n => Prosa.Util.Sum.sumSeq (List.range' (xs.length - n) (xs.length - (xs.length - n))) fun t => xs.getD t 0
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_suffix_sum
     : List_inst1 Nat -> Nat -> Nat
```

Body:

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_suffix_sum@{} =
fun (xs : List_inst1 Nat) (n : Nat) =>
Prosa_Util_Sum_sumSeq_inst1 Nat
  (List_range' (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) (List_length_inst1 Nat xs) n)
     (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) (List_length_inst1 Nat xs)
        (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) (List_length_inst1 Nat xs) n))
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
  (fun t : Nat => List_getD_inst1 Nat xs t (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
     : List_inst1 Nat -> Nat -> Nat

Arguments Prosa_Implementation_Definitions_MaximalArrivalSequence_suffix_sum xs n%_Nat_scope
```
