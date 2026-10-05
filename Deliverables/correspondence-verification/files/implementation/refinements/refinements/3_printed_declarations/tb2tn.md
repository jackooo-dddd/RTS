# `tb2tn`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.tb2tn`
- Lean: `Prosa.Implementation.Refinements.Refinements.tb2tn`
- Certificate: `tb2tn_correspondence`

## Official Rocq

```coq
tb2tn : N * N -> nat * nat

tb2tn is not universe polymorphic
Arguments tb2tn t
tb2tn is transparent
Expands to: Constant prosa.implementation.refinements.refinements.tb2tn
Declared in library prosa.implementation.refinements.refinements, line 42, characters 11-16
tb2tn
     : N * N -> nat * nat
```

Body:

```coq
tb2tn = [eta @tmap N nat nat_of_bin]
     : N * N -> nat * nat

Arguments tb2tn t
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.tb2tn : Prosa.Implementation.Refinements.Refinements.N ×
    Prosa.Implementation.Refinements.Refinements.N →
  ℕ × ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.tb2tn : Prosa.Implementation.Refinements.Refinements.N ×
    Prosa.Implementation.Refinements.Refinements.N →
  ℕ × ℕ :=
fun t => Prosa.Implementation.Refinements.Refinements.tmap Prosa.Implementation.Refinements.Refinements.nat_of_bin t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_tb2tn
     : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         Prosa_Implementation_Refinements_Refinements_N ->
       Prod_inst3 Nat Nat
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_tb2tn@{} =
fun
  t : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
        Prosa_Implementation_Refinements_Refinements_N =>
Prosa_Implementation_Refinements_Refinements_tmap Prosa_Implementation_Refinements_Refinements_N Nat
  Prosa_Implementation_Refinements_Refinements_nat_of_bin t
     : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         Prosa_Implementation_Refinements_Refinements_N ->
       Prod_inst3 Nat Nat

Arguments Prosa_Implementation_Refinements_Refinements_tb2tn t
```
