# `big_sum_eq_in_eq_sized_intervals`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.big_sum_eq_in_eq_sized_intervals`
- Lean: `Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals`
- Certificate: `big_sum_eq_in_eq_sized_intervals_statement_certificate`

## Official Rocq

```coq
big_sum_eq_in_eq_sized_intervals :
forall (t1 t2 d : nat) (F1 F2 : nat -> nat),
(forall g : nat, is_true (g < d) -> F1 (t1 + g) = F2 (t2 + g)) ->
@bigop.bigop.body nat nat 0 (bigop.index_iota t1 (t1 + d))
  (fun t : nat => @bigop.BigBody nat nat t addn true (F1 t)) =
@bigop.bigop.body nat nat 0 (bigop.index_iota t2 (t2 + d))
  (fun t : nat => @bigop.BigBody nat nat t addn true (F2 t))

big_sum_eq_in_eq_sized_intervals is not universe polymorphic
Arguments big_sum_eq_in_eq_sized_intervals (t1 t2 d)%nat_scope (F1 F2 equal_before_d)%function_scope
big_sum_eq_in_eq_sized_intervals is opaque
Expands to: Constant prosa.util.sum.big_sum_eq_in_eq_sized_intervals
Declared in library prosa.util.sum, line 291, characters 8-40
big_sum_eq_in_eq_sized_intervals
     : forall (t1 t2 d : nat) (F1 F2 : nat -> nat),
       (forall g : nat, is_true (g < d) -> F1 (t1 + g) = F2 (t2 + g)) ->
       @bigop.bigop.body nat nat 0 (bigop.index_iota t1 (t1 + d))
         (fun t : nat => @bigop.BigBody nat nat t addn true (F1 t)) =
       @bigop.bigop.body nat nat 0 (bigop.index_iota t2 (t2 + d))
         (fun t : nat => @bigop.BigBody nat nat t addn true (F2 t))
```

## Lean

```lean
Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals : ∀ (t1 t2 d : ℕ) (F1 F2 : ℕ → ℕ),
  (∀ g < d, F1 (t1 + g) = F2 (t2 + g)) → ∑ t ∈ Finset.Ico t1 (t1 + d), F1 t = ∑ t ∈ Finset.Ico t2 (t2 + d), F2 t
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_big_sum_eq_in_eq_sized_intervals
     : forall (t1 t2 d : Nat) (F1 F2 : Nat -> Nat),
       (forall g : Nat,
        LT_lt_inst1 Nat instLTNat g d ->
        @eq Nat (F1 (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t1 g))
          (F2 (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t2 g))) ->
       @eq Nat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun x : Nat => F1 x)
               (List_range' t1
                  (Nat_sub (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t1 d) t1) 1)))
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun t : Nat => F2 t)
               (List_range' t2
                  (Nat_sub (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t2 d) t2) 1)))
```
