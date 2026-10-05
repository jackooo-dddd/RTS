# `iotaTsuccN`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.refinements.iotaTsuccN`
- Lean: `Prosa.Implementation.Refinements.Refinements.iotaTsuccN`
- Certificate: `iotaTsuccN_correspondence`

## Official Rocq

```coq
iotaTsuccN :
forall (a : N) (p : positive),
@iota_T N one_N add_N a (nat_of_bin (N.succ (Pos.pred_N p))) =
a :: @iota_T N one_N add_N (succN a) (nat_of_bin (Pos.pred_N p))

iotaTsuccN is not universe polymorphic
Arguments iotaTsuccN a%_N_scope p%_positive_scope
iotaTsuccN is opaque
Expands to: Constant prosa.implementation.refinements.refinements.iotaTsuccN
Declared in library prosa.implementation.refinements.refinements, line 336, characters 6-16
iotaTsuccN
     : forall (a : N) (p : positive),
       @iota_T N one_N add_N a (nat_of_bin (N.succ (Pos.pred_N p))) =
       a :: @iota_T N one_N add_N (succN a) (nat_of_bin (Pos.pred_N p))
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.iotaTsuccN : ∀ (a : Prosa.Implementation.Refinements.Refinements.N)
  (p : Prosa.Implementation.Refinements.Refinements.positive),
  Prosa.Implementation.Refinements.Refinements.iota_T a
      (Prosa.Implementation.Refinements.Refinements.nat_of_bin
        (Prosa.Implementation.Refinements.Refinements.Pos.pred_N p).succ) =
    a ::
      Prosa.Implementation.Refinements.Refinements.iota_T (Prosa.Implementation.Refinements.Refinements.succN a)
        (Prosa.Implementation.Refinements.Refinements.nat_of_bin
          (Prosa.Implementation.Refinements.Refinements.Pos.pred_N p))
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_iotaTsuccN
     : forall (a : Prosa_Implementation_Refinements_Refinements_N)
         (p : Prosa_Implementation_Refinements_Refinements_positive),
       @eq (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_iota_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N a
            (Prosa_Implementation_Refinements_Refinements_nat_of_bin
               (Prosa_Implementation_Refinements_Refinements_N_succ
                  (Prosa_Implementation_Refinements_Refinements_Pos_pred_N p))))
         (List_cons_inst1 Prosa_Implementation_Refinements_Refinements_N a
            (Prosa_Implementation_Refinements_Refinements_iota_T
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_one_N
               Prosa_Implementation_Refinements_Refinements_add_N
               (Prosa_Implementation_Refinements_Refinements_succN a)
               (Prosa_Implementation_Refinements_Refinements_nat_of_bin
                  (Prosa_Implementation_Refinements_Refinements_Pos_pred_N p))))
```
