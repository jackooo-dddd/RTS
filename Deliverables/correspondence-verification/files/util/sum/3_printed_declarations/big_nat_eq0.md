# `big_nat_eq0`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.big_nat_eq0`
- Lean: `Prosa.Util.Sum.big_nat_eq0`
- Certificate: `big_nat_eq0_statement_certificate`

## Official Rocq

```coq
big_nat_eq0 :
forall (m n : nat) (F : nat -> nat),
@bigop.bigop.body nat nat 0 (bigop.index_iota m n) (fun i : nat => @bigop.BigBody nat nat i addn true (F i)) =
0 <-> (forall i : nat, is_true (m <= i < n) -> F i = 0)

big_nat_eq0 is not universe polymorphic
Arguments big_nat_eq0 (m n)%nat_scope F%function_scope
big_nat_eq0 is opaque
Expands to: Constant prosa.util.sum.big_nat_eq0
Declared in library prosa.util.sum, line 242, characters 6-17
big_nat_eq0
     : forall (m n : nat) (F : nat -> nat),
       @bigop.bigop.body nat nat 0 (bigop.index_iota m n)
         (fun i : nat => @bigop.BigBody nat nat i addn true (F i)) =
       0 <-> (forall i : nat, is_true (m <= i < n) -> F i = 0)
```

## Lean

```lean
Prosa.Util.Sum.big_nat_eq0 : ∀ (m n : ℕ) (F : ℕ → ℕ), ∑ i ∈ Finset.Ico m n, F i = 0 ↔ ∀ (i : ℕ), m ≤ i ∧ i < n → F i = 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_big_nat_eq0
     : forall (m n : Nat) (F : Nat -> Nat),
       Iff
         (@eq Nat
            (List_foldr_inst3 Nat Nat Nat_add 0
               (List_map_inst3 Nat Nat
                  (fun n____at___Init_Prelude427477602__hygCtx__hyg40 : Nat =>
                   F n____at___Init_Prelude427477602__hygCtx__hyg40)
                  (List_range' m (Nat_sub n m) 1)))
            (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
         (forall i : Nat,
          And (LE_le_inst1 Nat instLENat m i) (LT_lt_inst1 Nat instLTNat i n) ->
          @eq Nat (F i) (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
```
