# `last0_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.last0_cat`
- Lean: `Prosa.Util.List.last0_cat`
- Certificate: `last0_cat_statement_certificate`

## Official Rocq

```coq
last0_cat : forall xs_l xs_r : seq nat, xs_r <> [::] -> last0 (xs_l ++ xs_r) = last0 xs_r

last0_cat is not universe polymorphic
Arguments last0_cat (xs_l xs_r)%seq_scope _
last0_cat is opaque
Expands to: Constant prosa.util.list.last0_cat
Declared in library prosa.util.list, line 27, characters 6-15
last0_cat
     : forall xs_l xs_r : seq nat, xs_r <> [::] -> last0 (xs_l ++ xs_r) = last0 xs_r
```

## Lean

```lean
Prosa.Util.List.last0_cat : ∀ (xs_l xs_r : List ℕ),
  xs_r ≠ [] → Prosa.Util.List.last0 (xs_l ++ xs_r) = Prosa.Util.List.last0 xs_r
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_last0_cat
     : forall xs_l xs_r : List_inst1 Nat,
       Ne (List_inst1 Nat) xs_r (List_nil_inst1 Nat) ->
       @eq Nat
         (Prosa_Util_List_last0
            (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
               (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat)) xs_l xs_r))
         (Prosa_Util_List_last0 xs_r)
```
