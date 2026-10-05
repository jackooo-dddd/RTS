# `sum_le_summation_range`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_le_summation_range`
- Lean: `Prosa.Util.Sum.sum_le_summation_range`
- Certificate: `sum_le_summation_range_statement_certificate`

## Official Rocq

```coq
sum_le_summation_range :
forall (f : nat -> nat) (t Δ : nat),
is_true
  (@bigop.bigop.body nat nat 0 (bigop.index_iota t (t + Δ))
     (fun x : nat => @bigop.BigBody nat nat x addn true (f x)) <
   Δ) ->
exists x : nat, is_true (t <= x < t + Δ) /\ f x = 0

sum_le_summation_range is not universe polymorphic
Arguments sum_le_summation_range f%function_scope (t Δ)%nat_scope _
sum_le_summation_range is opaque
Expands to: Constant prosa.util.sum.sum_le_summation_range
Declared in library prosa.util.sum, line 257, characters 6-28
sum_le_summation_range
     : forall (f : nat -> nat) (t Δ : nat),
       is_true
         (@bigop.bigop.body nat nat 0 (bigop.index_iota t (t + Δ))
            (fun x : nat => @bigop.BigBody nat nat x addn true (f x)) <
          Δ) ->
       exists x : nat, is_true (t <= x < t + Δ) /\ f x = 0
```

## Lean

```lean
Prosa.Util.Sum.sum_le_summation_range : ∀ (f : ℕ → ℕ) (t Δ : ℕ),
  ∑ x ∈ Finset.Ico t (t + Δ), f x < Δ → ∃ x, t ≤ x ∧ x < t + Δ ∧ f x = 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_le_summation_range
     : forall (f : Nat -> Nat) (t _UU0394_ : Nat),
       LT_lt_inst1 Nat instLTNat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun x : Nat => f x)
               (List_range' t
                  (Nat_sub (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t _UU0394_) t) 1)))
         _UU0394_ ->
       Exists Nat
         (fun x : Nat =>
          And (LE_le_inst1 Nat instLENat t x)
            (And
               (LT_lt_inst1 Nat instLTNat x
                  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t _UU0394_))
               (@eq Nat (f x) (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))))
```
