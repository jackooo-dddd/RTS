# `subnACA`

- Kind (Rocq): Fact
- Rocq: `prosa.util.nat.subnACA`
- Lean: `Prosa.Util.Nat.subnACA`
- Certificate: `subnACA_correspondence_certificate`

## Official Rocq

```coq
subnACA : forall {m n p q : nat}, is_true (p <= m) -> is_true (q <= n) -> m + n - (p + q) = m - p + (n - q)

subnACA is not universe polymorphic
Arguments subnACA {m n p q}%nat_scope _ _
subnACA is opaque
Expands to: Constant prosa.util.nat.subnACA
Declared in library prosa.util.nat, line 11, characters 5-12
@subnACA
     : forall m n p q : nat, is_true (p <= m) -> is_true (q <= n) -> m + n - (p + q) = m - p + (n - q)
```

## Lean

```lean
@Prosa.Util.Nat.subnACA : ∀ {m n p q : ℕ}, p ≤ m → q ≤ n → m + n - (p + q) = m - p + (n - q)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nat_subnACA
     : forall m n p q : Nat,
       LE_le_inst1 Nat instLENat p m ->
       LE_le_inst1 Nat instLENat q n ->
       @eq Nat
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) m n)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) p q))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) m p)
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) n q))
```
