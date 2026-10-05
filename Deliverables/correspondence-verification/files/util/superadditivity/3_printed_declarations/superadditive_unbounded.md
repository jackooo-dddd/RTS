# `superadditive_unbounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.superadditivity.superadditive_unbounded`
- Lean: `Prosa.Util.Superadditivity.superadditive_unbounded`
- Certificate: `superadditivity_unbounded_statement_certificate`

## Official Rocq

```coq
superadditive_unbounded :
forall f : nat -> nat,
superadditive f ->
(exists n : nat, is_true (0 < f n)) -> forall t : nat, exists n' : nat, is_true (t <= f n')

superadditive_unbounded is not universe polymorphic
Arguments superadditive_unbounded f%function_scope h_superadditive h_non_zero t%nat_scope
superadditive_unbounded is opaque
Expands to: Constant prosa.util.superadditivity.superadditive_unbounded
Declared in library prosa.util.superadditivity, line 111, characters 12-35
superadditive_unbounded
     : forall f : nat -> nat,
       superadditive f ->
       (exists n : nat, is_true (0 < f n)) -> forall t : nat, exists n' : nat, is_true (t <= f n')
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive_unbounded : ∀ (f : ℕ → ℕ),
  Prosa.Util.Superadditivity.superadditive f → (∃ n, 0 < f n) → ∀ (t : ℕ), ∃ n', t ≤ f n'
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive_unbounded
     : forall f : Nat -> Nat,
       Prosa_Util_Superadditivity_superadditive f ->
       Exists Nat (fun n : Nat => LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) (f n)) ->
       forall t : Nat, Exists Nat (fun n' : Nat => LE_le_inst1 Nat instLENat t (f n'))
```
