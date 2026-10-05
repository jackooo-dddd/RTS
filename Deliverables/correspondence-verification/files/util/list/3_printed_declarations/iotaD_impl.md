# `iotaD_impl`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.iotaD_impl`
- Lean: `Prosa.Util.List.iotaD_impl`
- Certificate: `iotaD_impl_statement_certificate`

## Official Rocq

```coq
iotaD_impl :
forall n_le m n : nat, is_true (n_le <= n) -> iota m n = iota m n_le ++ iota (m + n_le) (n - n_le)

iotaD_impl is not universe polymorphic
Arguments iotaD_impl (n_le m n)%nat_scope _
iotaD_impl is opaque
Expands to: Constant prosa.util.list.iotaD_impl
Declared in library prosa.util.list, line 639, characters 6-16
iotaD_impl
     : forall n_le m n : nat, is_true (n_le <= n) -> iota m n = iota m n_le ++ iota (m + n_le) (n - n_le)
```

## Lean

```lean
Prosa.Util.List.iotaD_impl : ∀ (n_le m n : ℕ),
  n_le ≤ n → List.range' m n = List.range' m n_le ++ List.range' (m + n_le) (n - n_le)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_iotaD_impl
     : forall n_le m n : Nat,
       LE_le_inst1 Nat instLENat n_le n ->
       @eq (List_inst1 Nat) (List_range' m n (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
         (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
            (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat))
            (List_range' m n_le (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            (List_range' (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) m n_le)
               (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) n n_le)
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
```
