# `index_iota_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.index_iota_cat`
- Lean: `Prosa.Util.List.index_iota_cat`
- Certificate: `index_iota_cat_statement_certificate`

## Official Rocq

```coq
index_iota_cat :
forall t t1 t2 : nat,
is_true (t1 <= t <= t2) -> bigop.index_iota t1 t2 = bigop.index_iota t1 t ++ bigop.index_iota t t2

index_iota_cat is not universe polymorphic
Arguments index_iota_cat (t t1 t2)%nat_scope _
index_iota_cat is opaque
Expands to: Constant prosa.util.list.index_iota_cat
Declared in library prosa.util.list, line 663, characters 6-20
index_iota_cat
     : forall t t1 t2 : nat,
       is_true (t1 <= t <= t2) -> bigop.index_iota t1 t2 = bigop.index_iota t1 t ++ bigop.index_iota t t2
```

## Lean

```lean
Prosa.Util.List.index_iota_cat : ∀ (t t1 t2 : ℕ),
  t1 ≤ t ∧ t ≤ t2 →
    Prosa.Util.List.index_iota t1 t2 = Prosa.Util.List.index_iota t1 t ++ Prosa.Util.List.index_iota t t2
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_index_iota_cat
     : forall t t1 t2 : Nat,
       And (LE_le_inst1 Nat instLENat t1 t) (LE_le_inst1 Nat instLENat t t2) ->
       @eq (List_inst1 Nat) (Prosa_Util_List_index_iota t1 t2)
         (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
            (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat))
            (Prosa_Util_List_index_iota t1 t) (Prosa_Util_List_index_iota t t2))
```
