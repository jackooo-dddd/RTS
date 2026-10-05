# `eq_SnPos_to_nPred`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.refinements.eq_SnPos_to_nPred`
- Lean: `Prosa.Implementation.Refinements.Refinements.eq_SnPos_to_nPred`
- Certificate: `eq_SnPos_to_nPred_correspondence`

## Official Rocq

```coq
eq_SnPos_to_nPred : forall (b : nat) (p : positive), Rnat b.+1 (N.pos p) -> Rnat b (Pos.pred_N p)

eq_SnPos_to_nPred is not universe polymorphic
Arguments eq_SnPos_to_nPred b%_nat_scope p%_positive_scope _
eq_SnPos_to_nPred is opaque
Expands to: Constant prosa.implementation.refinements.refinements.eq_SnPos_to_nPred
Declared in library prosa.implementation.refinements.refinements, line 184, characters 6-23
eq_SnPos_to_nPred
     : forall (b : nat) (p : positive), Rnat b.+1 (N.pos p) -> Rnat b (Pos.pred_N p)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.eq_SnPos_to_nPred : (b : ℕ) →
  (p : Prosa.Implementation.Refinements.Refinements.positive) →
    Prosa.Implementation.Refinements.Refinements.Rnat (b + 1) (Prosa.Implementation.Refinements.Refinements.N.Npos p) →
      Prosa.Implementation.Refinements.Refinements.Rnat b (Prosa.Implementation.Refinements.Refinements.Pos.pred_N p)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_eq_SnPos_to_nPred
     : forall (b : Nat) (p : Prosa_Implementation_Refinements_Refinements_positive),
       Prosa_Implementation_Refinements_Refinements_Rnat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) b
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
         (Prosa_Implementation_Refinements_Refinements_N_Npos p) ->
       Prosa_Implementation_Refinements_Refinements_Rnat b
         (Prosa_Implementation_Refinements_Refinements_Pos_pred_N p)
```
