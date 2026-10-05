# `sum_of_ones`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_of_ones`
- Lean: `Prosa.Util.Sum.sum_of_ones`
- Certificate: `sum_of_ones_statement_certificate`

## Official Rocq

```coq
sum_of_ones :
forall t Δ : nat,
@bigop.bigop.body nat nat 0 (bigop.index_iota t (t + Δ))
  (fun x : nat => @bigop.BigBody nat nat x addn true 1) =
Δ

sum_of_ones is not universe polymorphic
Arguments sum_of_ones (t Δ)%nat_scope
sum_of_ones is opaque
Expands to: Constant prosa.util.sum.sum_of_ones
Declared in library prosa.util.sum, line 235, characters 6-17
sum_of_ones
     : forall t Δ : nat,
       @bigop.bigop.body nat nat 0 (bigop.index_iota t (t + Δ))
         (fun x : nat => @bigop.BigBody nat nat x addn true 1) =
       Δ
```

## Lean

```lean
Prosa.Util.Sum.sum_of_ones : ∀ (t Δ : ℕ), ∑ x ∈ Finset.Ico t (t + Δ), 1 = Δ
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_of_ones
     : forall t _UU0394_ : Nat,
       @eq Nat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun _ : Nat => OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
               (List_range' t
                  (Nat_sub (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t _UU0394_) t) 1)))
         _UU0394_
```
