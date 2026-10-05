# `leq_subRL_impl`

- Kind (Rocq): Fact
- Rocq: `prosa.util.nat.leq_subRL_impl`
- Lean: `Prosa.Util.Nat.leq_subRL_impl`
- Certificate: `leq_subRL_impl_correspondence_certificate`

## Official Rocq

```coq
leq_subRL_impl : forall {m n p : nat}, is_true (m + n <= p) -> is_true (n <= p - m)

leq_subRL_impl is not universe polymorphic
Arguments leq_subRL_impl {m n p}%nat_scope _
leq_subRL_impl is opaque
Expands to: Constant prosa.util.nat.leq_subRL_impl
Declared in library prosa.util.nat, line 19, characters 5-19
@leq_subRL_impl
     : forall m n p : nat, is_true (m + n <= p) -> is_true (n <= p - m)
```

## Lean

```lean
@Prosa.Util.Nat.leq_subRL_impl : ∀ {m n p : ℕ}, m + n ≤ p → n ≤ p - m
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nat_leq_subRL_impl
     : forall m n p : Nat,
       LE_le_inst1 Nat instLENat (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) m n) p ->
       LE_le_inst1 Nat instLENat n (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) p m)
```
