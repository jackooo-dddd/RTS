# `last0_ex_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.last0_ex_cat`
- Lean: `Prosa.Util.List.last0_ex_cat`
- Certificate: `last0_ex_cat_statement_certificate`

## Official Rocq

```coq
last0_ex_cat :
forall (x : nat) (xs : seq nat), xs <> [::] -> last0 xs = x -> exists xsh : seq nat, xsh ++ [:: x] = xs

last0_ex_cat is not universe polymorphic
Arguments last0_ex_cat x%nat_scope xs%seq_scope _ _
last0_ex_cat is opaque
Expands to: Constant prosa.util.list.last0_ex_cat
Declared in library prosa.util.list, line 46, characters 6-18
last0_ex_cat
     : forall (x : nat) (xs : seq nat),
       xs <> [::] -> last0 xs = x -> exists xsh : seq nat, xsh ++ [:: x] = xs
```

## Lean

```lean
Prosa.Util.List.last0_ex_cat : ∀ (x : ℕ) (xs : List ℕ), xs ≠ [] → Prosa.Util.List.last0 xs = x → ∃ xsh, xsh ++ [x] = xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_last0_ex_cat
     : forall (x : Nat) (xs : List_inst1 Nat),
       Ne (List_inst1 Nat) xs (List_nil_inst1 Nat) ->
       @eq Nat (Prosa_Util_List_last0 xs) x ->
       Exists (List_inst1 Nat)
         (fun xsh : List_inst1 Nat =>
          HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
            (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat)) xsh
            (List_cons_inst1 Nat x (List_nil_inst1 Nat)) =
          xs)
```
