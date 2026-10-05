# `superadditive_leq_mul`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.superadditivity.superadditive_leq_mul`
- Lean: `Prosa.Util.Superadditivity.superadditive_leq_mul`
- Certificate: `superadditivity_leq_mul_statement_certificate`

## Official Rocq

```coq
superadditive_leq_mul :
forall f : nat -> nat, superadditive f -> forall n m : nat, is_true (m * f n <= f (m * n))

superadditive_leq_mul is not universe polymorphic
Arguments superadditive_leq_mul f%function_scope h_superadditive (n m)%nat_scope
superadditive_leq_mul is opaque
Expands to: Constant prosa.util.superadditivity.superadditive_leq_mul
Declared in library prosa.util.superadditivity, line 90, characters 10-31
superadditive_leq_mul
     : forall f : nat -> nat, superadditive f -> forall n m : nat, is_true (m * f n <= f (m * n))
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive_leq_mul : ∀ (f : ℕ → ℕ),
  Prosa.Util.Superadditivity.superadditive f → ∀ (n m : ℕ), m * f n ≤ f (m * n)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive_leq_mul
     : forall f : Nat -> Nat,
       Prosa_Util_Superadditivity_superadditive f ->
       forall n m : Nat,
       LE_le_inst1 Nat instLENat (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) m (f n))
         (f (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) m n))
```
