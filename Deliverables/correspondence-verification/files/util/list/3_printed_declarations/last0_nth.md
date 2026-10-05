# `last0_nth`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.last0_nth`
- Lean: `Prosa.Util.List.last0_nth`
- Certificate: `last0_nth_statement_certificate`

## Official Rocq

```coq
last0_nth : forall xs : seq nat, last0 xs = @nth nat 0 xs (@size nat xs).-1

last0_nth is not universe polymorphic
Arguments last0_nth xs%seq_scope
last0_nth is opaque
Expands to: Constant prosa.util.list.last0_nth
Declared in library prosa.util.list, line 39, characters 6-15
last0_nth
     : forall xs : seq nat, last0 xs = @nth nat 0 xs (@size nat xs).-1
```

## Lean

```lean
Prosa.Util.List.last0_nth : ∀ (xs : List ℕ), Prosa.Util.List.last0 xs = xs.getD (xs.length - 1) 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_last0_nth
     : forall xs : List_inst1 Nat,
       @eq Nat (Prosa_Util_List_last0 xs)
         (List_getD_inst1 Nat xs
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) (List_length_inst1 Nat xs)
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
```
