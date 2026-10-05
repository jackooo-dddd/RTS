# `refine_ltn`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.refinements.refine_ltn`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_ltn`
- Certificate: `refine_ltn_correspondence`

## Official Rocq

```coq
refine_ltn :
forall (a : nat) (a' : N) (b : nat) (b' : N), Rnat a a' -> Rnat b b' -> bool_R (a < b) (a' < b')%C

refine_ltn is not universe polymorphic
Arguments refine_ltn a%_nat_scope a'%_N_scope b%_nat_scope b'%_N_scope _ _
refine_ltn is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_ltn
Declared in library prosa.implementation.refinements.refinements, line 198, characters 6-16
refine_ltn
     : forall (a : nat) (a' : N) (b : nat) (b' : N), Rnat a a' -> Rnat b b' -> bool_R (a < b) (a' < b')%C
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_ltn : (a : ℕ) →
  (a' : Prosa.Implementation.Refinements.Refinements.N) →
    (b : ℕ) →
      (b' : Prosa.Implementation.Refinements.Refinements.N) →
        Prosa.Implementation.Refinements.Refinements.Rnat a a' →
          Prosa.Implementation.Refinements.Refinements.Rnat b b' →
            Prosa.Implementation.Refinements.Refinements.bool_R (decide (a < b))
              (Prosa.Implementation.Refinements.Refinements.lt_op a' b')
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_ltn
     : forall (a : Nat) (a' : Prosa_Implementation_Refinements_Refinements_N) (b : Nat)
         (b' : Prosa_Implementation_Refinements_Refinements_N),
       Prosa_Implementation_Refinements_Refinements_Rnat a a' ->
       Prosa_Implementation_Refinements_Refinements_Rnat b b' ->
       Prosa_Implementation_Refinements_Refinements_bool_R
         (Decidable_decide (LT_lt_inst1 Nat instLTNat a b) (Nat_decLt a b))
         (Prosa_Implementation_Refinements_Refinements_lt_of_lt_op
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_lt_N
            a' b')
```
