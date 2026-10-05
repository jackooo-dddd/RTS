# `sum_ge_2_nat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_ge_2_nat`
- Lean: `Prosa.Util.Sum.sum_ge_2_nat`
- Certificate: `sum_ge_2_nat_statement_certificate`

## Official Rocq

```coq
sum_ge_2_nat :
forall (t1 t2 : nat) (p : nat -> nat),
(forall t : nat, is_true (p t <= 1)) ->
is_true
  (1 <
   @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
     (fun t : nat => @bigop.BigBody nat nat t addn true (p t))) ->
exists to1 to2 : nat,
  is_true (t1 <= to1) /\
  is_true (to1 < to2) /\ is_true (to2 < t2) /\ is_true (p to1 == 1) /\ is_true (p to2 == 1)

sum_ge_2_nat is not universe polymorphic
Arguments sum_ge_2_nat (t1 t2)%nat_scope (p _)%function_scope _
sum_ge_2_nat is opaque
Expands to: Constant prosa.util.sum.sum_ge_2_nat
Declared in library prosa.util.sum, line 529, characters 6-18
sum_ge_2_nat
     : forall (t1 t2 : nat) (p : nat -> nat),
       (forall t : nat, is_true (p t <= 1)) ->
       is_true
         (1 <
          @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
            (fun t : nat => @bigop.BigBody nat nat t addn true (p t))) ->
       exists to1 to2 : nat,
         is_true (t1 <= to1) /\
         is_true (to1 < to2) /\ is_true (to2 < t2) /\ is_true (p to1 == 1) /\ is_true (p to2 == 1)
```

## Lean

```lean
Prosa.Util.Sum.sum_ge_2_nat : ∀ (t1 t2 : ℕ) (p : ℕ → ℕ),
  (∀ (t : ℕ), p t ≤ 1) →
    2 ≤ ∑ t ∈ Finset.Ico t1 t2, p t →
      ∃ to1 to2, t1 ≤ to1 ∧ to1 < to2 ∧ to2 < t2 ∧ decide (p to1 = 1) = true ∧ decide (p to2 = 1) = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_ge_2_nat
     : forall (t1 t2 : Nat) (p : Nat -> Nat),
       (forall t : Nat, LE_le_inst1 Nat instLENat (p t) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       LE_le_inst1 Nat instLENat (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2))
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun t : Nat => p t) (List_range' t1 (Nat_sub t2 t1) 1))) ->
       Exists Nat
         (fun to1 : Nat =>
          Exists Nat
            (fun to2 : Nat =>
             And (LE_le_inst1 Nat instLENat t1 to1)
               (And (LT_lt_inst1 Nat instLTNat to1 to2)
                  (And (LT_lt_inst1 Nat instLTNat to2 t2)
                     (And
                        (@eq Bool
                           (Decidable_decide (@eq Nat (p to1) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                              (instDecidableEqNat (p to1) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                           Bool_true)
                        (@eq Bool
                           (Decidable_decide (@eq Nat (p to2) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                              (instDecidableEqNat (p to2) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                           Bool_true))))))
```
