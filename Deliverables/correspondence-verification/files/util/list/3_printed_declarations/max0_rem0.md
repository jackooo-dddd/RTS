# `max0_rem0`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.max0_rem0`
- Lean: `Prosa.Util.List.max0_rem0`
- Certificate: `max0_rem0_statement_certificate`

## Official Rocq

```coq
max0_rem0 : forall xs : seq nat, max0 [seq x <- xs | 0 < x] = max0 xs

max0_rem0 is not universe polymorphic
Arguments max0_rem0 xs%seq_scope
max0_rem0 is opaque
Expands to: Constant prosa.util.list.max0_rem0
Declared in library prosa.util.list, line 150, characters 6-15
max0_rem0
     : forall xs : seq nat, max0 [seq x <- xs | 0 < x] = max0 xs
```

## Lean

```lean
Prosa.Util.List.max0_rem0 : ∀ (xs : List ℕ),
  Prosa.Util.List.max0 (List.filter (fun x => decide (0 < x)) xs) = Prosa.Util.List.max0 xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_max0_rem0
     : forall xs : List_inst1 Nat,
       @eq Nat
         (Prosa_Util_List_max0
            (List_filter_inst1 Nat
               (fun x : Nat =>
                Decidable_decide (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) x)
                  (Nat_decLt (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) x))
               xs))
         (Prosa_Util_List_max0 xs)
```
