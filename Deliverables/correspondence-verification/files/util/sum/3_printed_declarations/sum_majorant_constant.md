# `sum_majorant_constant`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_majorant_constant`
- Lean: `Prosa.Util.Sum.sum_majorant_constant`
- Certificate: `sum_majorant_constant_statement_certificate`

## Official Rocq

```coq
sum_majorant_constant :
forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat)
  (c : nat),
(forall a : Equality.sort I, is_true (a \in r) -> is_true (P a) -> is_true (F a <= c)) ->
is_true
  (@bigop.bigop.body nat (Equality.sort I) 0 r
     (fun j : Equality.sort I => @bigop.BigBody nat (Equality.sort I) j addn (P j) (F j)) <=
   c * @size (Equality.sort I) [seq j <- r | P j])

sum_majorant_constant is not universe polymorphic
Arguments sum_majorant_constant I r%seq_scope P F%function_scope c%nat_scope _%function_scope
sum_majorant_constant is opaque
Expands to: Constant prosa.util.sum.sum_majorant_constant
Declared in library prosa.util.sum, line 45, characters 10-31
sum_majorant_constant
     : forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (F : Equality.sort I -> nat) (c : nat),
       (forall a : Equality.sort I, is_true (a \in r) -> is_true (P a) -> is_true (F a <= c)) ->
       is_true
         (@bigop.bigop.body nat (Equality.sort I) 0 r
            (fun j : Equality.sort I => @bigop.BigBody nat (Equality.sort I) j addn (P j) (F j)) <=
          c * @size (Equality.sort I) [seq j <- r | P j])
```

## Lean

```lean
@Prosa.Util.Sum.sum_majorant_constant : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (P : I → Bool) (F : I → ℕ)
  (c : ℕ), (∀ a ∈ r, P a = true → F a ≤ c) → Prosa.Util.Sum.sumFiltered r P F ≤ c * (List.filter P r).length
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_majorant_constant
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) (F : I -> Nat) (c : Nat),
       (forall a : I,
        Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) r a ->
        @eq ImportedSumSequence.Bool (P a) ImportedSumSequence.Bool_true ->
        ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (F a) c) ->
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (Prosa_Util_Sum_sumFiltered I r P F)
         (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) c (List_length I (List_filter I P r)))
```
