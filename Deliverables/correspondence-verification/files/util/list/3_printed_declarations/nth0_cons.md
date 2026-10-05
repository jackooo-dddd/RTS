# `nth0_cons`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.nth0_cons`
- Lean: `Prosa.Util.List.nth0_cons`
- Certificate: `nth0_cons_statement_certificate`

## Official Rocq

```coq
nth0_cons :
forall (x : nat) (xs : seq nat) (n : nat), is_true (0 < n) -> @nth nat 0 (x :: xs) n = @nth nat 0 xs n.-1

nth0_cons is not universe polymorphic
Arguments nth0_cons x%nat_scope xs%seq_scope n%nat_scope _
nth0_cons is opaque
Expands to: Constant prosa.util.list.nth0_cons
Declared in library prosa.util.list, line 299, characters 6-15
nth0_cons
     : forall (x : nat) (xs : seq nat) (n : nat),
       is_true (0 < n) -> @nth nat 0 (x :: xs) n = @nth nat 0 xs n.-1
```

## Lean

```lean
Prosa.Util.List.nth0_cons : ∀ (x : ℕ) (xs : List ℕ) (n : ℕ), n > 0 → (x :: xs).getD n 0 = xs.getD (n - 1) 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_nth0_cons
     : forall (x : Nat) (xs : List_inst1 Nat) (n : Nat),
       GT_gt_inst1 Nat instLTNat n (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) ->
       @eq Nat (List_getD_inst1 Nat (List_cons_inst1 Nat x xs) n (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
         (List_getD_inst1 Nat xs
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) n
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
```
