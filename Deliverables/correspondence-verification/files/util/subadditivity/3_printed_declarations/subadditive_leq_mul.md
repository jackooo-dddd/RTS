# `subadditive_leq_mul`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.subadditivity.subadditive_leq_mul`
- Lean: `Prosa.Util.Subadditivity.subadditive_leq_mul`
- Certificate: `subadditive_leq_mul_statement_certificate`

## Official Rocq

```coq
subadditive_leq_mul :
forall f : nat -> nat, subadditive f -> forall n m : nat, is_true (0 < m) -> is_true (f (m * n) <= m * f n)

subadditive_leq_mul is not universe polymorphic
Arguments subadditive_leq_mul f%function_scope h_subadditive (n m)%nat_scope _
subadditive_leq_mul is opaque
Expands to: Constant prosa.util.subadditivity.subadditive_leq_mul
Declared in library prosa.util.subadditivity, line 64, characters 10-29
subadditive_leq_mul
     : forall f : nat -> nat,
       subadditive f -> forall n m : nat, is_true (0 < m) -> is_true (f (m * n) <= m * f n)
```

## Lean

```lean
Prosa.Util.Subadditivity.subadditive_leq_mul : ∀ (f : ℕ → ℕ),
  Prosa.Util.Subadditivity.subadditive f → ∀ (n m : ℕ), 0 < m → f (m * n) ≤ m * f n
```

## Lean, imported into Rocq

```coq
Prosa_Util_Subadditivity_subadditive_leq_mul
     : forall f : Nat -> Nat,
       Prosa_Util_Subadditivity_subadditive f ->
       forall n m : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) m ->
       LE_le_inst1 Nat instLENat (f (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) m n))
         (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) m (f n))
```
