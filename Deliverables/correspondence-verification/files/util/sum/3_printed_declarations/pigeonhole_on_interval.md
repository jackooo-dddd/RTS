# `pigeonhole_on_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.pigeonhole_on_interval`
- Lean: `Prosa.Util.Sum.pigeonhole_on_interval`
- Certificate: `pigeonhole_on_interval_statement_certificate`

## Official Rocq

```coq
pigeonhole_on_interval :
forall (P1 P2 : pred nat) (t1 t2 n1 n2 : nat),
is_true
  (n1 <=
   @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
     (fun t : nat => @bigop.BigBody nat nat t addn true (nat_of_bool (P1 t)))) ->
is_true
  (n2 <=
   @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
     (fun t : nat => @bigop.BigBody nat nat t addn true (nat_of_bool (P2 t)))) ->
is_true
  (n1 + n2 - (t2 - t1) <=
   @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
     (fun t : nat => @bigop.BigBody nat nat t addn true (nat_of_bool (P1 t && P2 t))))

pigeonhole_on_interval is not universe polymorphic
Arguments pigeonhole_on_interval P1 P2 (t1 t2 n1 n2)%nat_scope _ _
pigeonhole_on_interval is opaque
Expands to: Constant prosa.util.sum.pigeonhole_on_interval
Declared in library prosa.util.sum, line 461, characters 6-28
pigeonhole_on_interval
     : forall (P1 P2 : pred nat) (t1 t2 n1 n2 : nat),
       is_true
         (n1 <=
          @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
            (fun t : nat => @bigop.BigBody nat nat t addn true (nat_of_bool (P1 t)))) ->
       is_true
         (n2 <=
          @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
            (fun t : nat => @bigop.BigBody nat nat t addn true (nat_of_bool (P2 t)))) ->
       is_true
         (n1 + n2 - (t2 - t1) <=
          @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
            (fun t : nat => @bigop.BigBody nat nat t addn true (nat_of_bool (P1 t && P2 t))))
```

## Lean

```lean
Prosa.Util.Sum.pigeonhole_on_interval : ∀ (P1 P2 : ℕ → Bool) (t1 t2 n1 n2 : ℕ),
  n1 ≤ ∑ t ∈ Finset.Ico t1 t2, (P1 t).toNat →
    n2 ≤ ∑ t ∈ Finset.Ico t1 t2, (P2 t).toNat → n1 + n2 - (t2 - t1) ≤ ∑ t ∈ Finset.Ico t1 t2, (P1 t && P2 t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_pigeonhole_on_interval
     : forall (P1 P2 : Nat -> Bool) (t1 t2 n1 n2 : Nat),
       LE_le_inst1 Nat instLENat n1
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun t : Nat => Bool_toNat (P1 t)) (List_range' t1 (Nat_sub t2 t1) 1))) ->
       LE_le_inst1 Nat instLENat n2
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun t : Nat => Bool_toNat (P2 t)) (List_range' t1 (Nat_sub t2 t1) 1))) ->
       LE_le_inst1 Nat instLENat
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n1 n2)
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t2 t1))
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun t : Nat => Bool_toNat (Bool_and (P1 t) (P2 t)))
               (List_range' t1 (Nat_sub t2 t1) 1)))
```
