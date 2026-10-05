# `last0_filter`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.last0_filter`
- Lean: `Prosa.Util.List.last0_filter`
- Certificate: `last0_filter_statement_certificate`

## Official Rocq

```coq
last0_filter :
forall (x : nat) (xs : seq nat) (P : nat -> bool),
xs <> [::] -> last0 xs = x -> is_true (P x) -> last0 [seq x0 <- xs | P x0] = x

last0_filter is not universe polymorphic
Arguments last0_filter x%nat_scope xs%seq_scope P%function_scope _ _ _
last0_filter is opaque
Expands to: Constant prosa.util.list.last0_filter
Declared in library prosa.util.list, line 63, characters 6-18
last0_filter
     : forall (x : nat) (xs : seq nat) (P : nat -> bool),
       xs <> [::] -> last0 xs = x -> is_true (P x) -> last0 [seq x0 <- xs | P x0] = x
```

## Lean

```lean
Prosa.Util.List.last0_filter : ∀ (x : ℕ) (xs : List ℕ) (P : ℕ → Bool),
  xs ≠ [] → Prosa.Util.List.last0 xs = x → P x = true → Prosa.Util.List.last0 (List.filter P xs) = x
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_last0_filter
     : forall (x : Nat) (xs : List_inst1 Nat) (P : Nat -> Bool),
       Ne (List_inst1 Nat) xs (List_nil_inst1 Nat) ->
       @eq Nat (Prosa_Util_List_last0 xs) x ->
       @eq Bool (P x) Bool_true -> @eq Nat (Prosa_Util_List_last0 (List_filter_inst1 Nat P xs)) x
```
