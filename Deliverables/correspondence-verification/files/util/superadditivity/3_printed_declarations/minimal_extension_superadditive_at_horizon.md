# `minimal_extension_superadditive_at_horizon`

- Kind (Rocq): Theorem
- Rocq: `prosa.util.superadditivity.minimal_extension_superadditive_at_horizon`
- Lean: `Prosa.Util.Superadditivity.minimal_extension_superadditive_at_horizon`
- Certificate: `sa_horizon_at_statement_certificate`

## Official Rocq

```coq
minimal_extension_superadditive_at_horizon :
forall (f : nat -> nat) (h : nat),
superadditive_until f h ->
forall f' : nat -> nat,
(forall t : nat, f' t = (if t == h then minimal_superadditive_extension f h else f t)) ->
superadditive_at f' h

minimal_extension_superadditive_at_horizon is not universe polymorphic
Arguments minimal_extension_superadditive_at_horizon f%function_scope h%nat_scope 
  h_superadditive_until (f' h_f'_min_extension)%function_scope a b _
minimal_extension_superadditive_at_horizon is opaque
Expands to: Constant prosa.util.superadditivity.minimal_extension_superadditive_at_horizon
Declared in library prosa.util.superadditivity, line 180, characters 12-54
minimal_extension_superadditive_at_horizon
     : forall (f : nat -> nat) (h : nat),
       superadditive_until f h ->
       forall f' : nat -> nat,
       (forall t : nat, f' t = (if t == h then minimal_superadditive_extension f h else f t)) ->
       superadditive_at f' h
```

## Lean

```lean
Prosa.Util.Superadditivity.minimal_extension_superadditive_at_horizon : ∀ (f : ℕ → ℕ) (h : ℕ),
  Prosa.Util.Superadditivity.superadditive_until f h →
    ∀ (f' : ℕ → ℕ),
      (∀ (t : ℕ),
          f' t =
            if decide (t = h) = true then Prosa.Util.Superadditivity.minimal_superadditive_extension f h else f t) →
        Prosa.Util.Superadditivity.superadditive_at f' h
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_minimal_extension_superadditive_at_horizon
     : forall (f : Nat -> Nat) (h : Nat),
       Prosa_Util_Superadditivity_superadditive_until f h ->
       forall f' : Nat -> Nat,
       (forall t : Nat,
        @eq Nat (f' t)
          (ite Nat (@eq Bool (Decidable_decide (@eq Nat t h) (instDecidableEqNat t h)) Bool_true)
             (instDecidableEqBool (Decidable_decide (@eq Nat t h) (instDecidableEqNat t h)) Bool_true)
             (Prosa_Util_Superadditivity_minimal_superadditive_extension f h) (f t))) ->
       Prosa_Util_Superadditivity_superadditive_at f' h
```
