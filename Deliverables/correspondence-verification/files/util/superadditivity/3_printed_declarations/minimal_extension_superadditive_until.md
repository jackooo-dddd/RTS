# `minimal_extension_superadditive_until`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.superadditivity.minimal_extension_superadditive_until`
- Lean: `Prosa.Util.Superadditivity.minimal_extension_superadditive_until`
- Certificate: `sa_horizon_until_statement_certificate`

## Official Rocq

```coq
minimal_extension_superadditive_until :
forall (f : nat -> nat) (h : nat),
superadditive_until f h ->
forall f' : nat -> nat,
(forall t : nat, f' t = (if t == h then minimal_superadditive_extension f h else f t)) ->
superadditive_until f' h.+1

minimal_extension_superadditive_until is not universe polymorphic
Arguments minimal_extension_superadditive_until f%function_scope h%nat_scope h_superadditive_until
  (f' h_f'_min_extension)%function_scope x _ a b _
minimal_extension_superadditive_until is opaque
Expands to: Constant prosa.util.superadditivity.minimal_extension_superadditive_until
Declared in library prosa.util.superadditivity, line 202, characters 10-47
minimal_extension_superadditive_until
     : forall (f : nat -> nat) (h : nat),
       superadditive_until f h ->
       forall f' : nat -> nat,
       (forall t : nat, f' t = (if t == h then minimal_superadditive_extension f h else f t)) ->
       superadditive_until f' h.+1
```

## Lean

```lean
Prosa.Util.Superadditivity.minimal_extension_superadditive_until : ∀ (f : ℕ → ℕ) (h : ℕ),
  Prosa.Util.Superadditivity.superadditive_until f h →
    ∀ (f' : ℕ → ℕ),
      (∀ (t : ℕ),
          f' t =
            if decide (t = h) = true then Prosa.Util.Superadditivity.minimal_superadditive_extension f h else f t) →
        Prosa.Util.Superadditivity.superadditive_until f' (h + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_minimal_extension_superadditive_until
     : forall (f : Nat -> Nat) (h : Nat),
       Prosa_Util_Superadditivity_superadditive_until f h ->
       forall f' : Nat -> Nat,
       (forall t : Nat,
        @eq Nat (f' t)
          (ite Nat (@eq Bool (Decidable_decide (@eq Nat t h) (instDecidableEqNat t h)) Bool_true)
             (instDecidableEqBool (Decidable_decide (@eq Nat t h) (instDecidableEqNat t h)) Bool_true)
             (Prosa_Util_Superadditivity_minimal_superadditive_extension f h) (f t))) ->
       Prosa_Util_Superadditivity_superadditive_until f'
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) h
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
```
