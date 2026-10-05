# `max_of_dominating_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.max_of_dominating_seq`
- Lean: `Prosa.Util.List.max_of_dominating_seq`
- Certificate: `max_of_dominating_seq_statement_certificate`

## Official Rocq

```coq
max_of_dominating_seq :
forall xs ys : seq nat,
(forall n : nat, is_true (@nth nat 0 xs n <= @nth nat 0 ys n)) -> is_true (max0 xs <= max0 ys)

max_of_dominating_seq is not universe polymorphic
Arguments max_of_dominating_seq (xs ys)%seq_scope _%function_scope
max_of_dominating_seq is opaque
Expands to: Constant prosa.util.list.max_of_dominating_seq
Declared in library prosa.util.list, line 182, characters 6-27
max_of_dominating_seq
     : forall xs ys : seq nat,
       (forall n : nat, is_true (@nth nat 0 xs n <= @nth nat 0 ys n)) -> is_true (max0 xs <= max0 ys)
```

## Lean

```lean
Prosa.Util.List.max_of_dominating_seq : ∀ (xs ys : List ℕ),
  (∀ (n : ℕ), xs.getD n 0 ≤ ys.getD n 0) → Prosa.Util.List.max0 xs ≤ Prosa.Util.List.max0 ys
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_max_of_dominating_seq
     : forall xs ys : List_inst1 Nat,
       (forall n : Nat,
        LE_le_inst1 Nat instLENat (List_getD_inst1 Nat xs n (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
          (List_getD_inst1 Nat ys n (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))) ->
       LE_le_inst1 Nat instLENat (Prosa_Util_List_max0 xs) (Prosa_Util_List_max0 ys)
```
