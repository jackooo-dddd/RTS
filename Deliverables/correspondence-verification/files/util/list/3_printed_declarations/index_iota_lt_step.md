# `index_iota_lt_step`

- Kind (Rocq): Remark
- Rocq: `prosa.util.list.index_iota_lt_step`
- Lean: `Prosa.Util.List.index_iota_lt_step`
- Certificate: `index_iota_lt_step_statement_certificate`

## Official Rocq

```coq
index_iota_lt_step : forall a b : nat, is_true (a < b) -> bigop.index_iota a b = a :: bigop.index_iota a.+1 b

index_iota_lt_step is not universe polymorphic
Arguments index_iota_lt_step (a b)%nat_scope _
index_iota_lt_step is opaque
Expands to: Constant prosa.util.list.index_iota_lt_step
Declared in library prosa.util.list, line 651, characters 7-25
index_iota_lt_step
     : forall a b : nat, is_true (a < b) -> bigop.index_iota a b = a :: bigop.index_iota a.+1 b
```

## Lean

```lean
Prosa.Util.List.index_iota_lt_step : ∀ (a b : ℕ),
  a < b → Prosa.Util.List.index_iota a b = a :: Prosa.Util.List.index_iota (a + 1) b
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_index_iota_lt_step
     : forall a b : Nat,
       LT_lt_inst1 Nat instLTNat a b ->
       @eq (List_inst1 Nat) (Prosa_Util_List_index_iota a b)
         (List_cons_inst1 Nat a
            (Prosa_Util_List_index_iota
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) a
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
               b))
```
