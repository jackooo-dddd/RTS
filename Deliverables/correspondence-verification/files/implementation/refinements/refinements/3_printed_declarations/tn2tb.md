# `tn2tb`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.tn2tb`
- Lean: `Prosa.Implementation.Refinements.Refinements.tn2tb`
- Certificate: `tn2tb_correspondence`

## Official Rocq

```coq
tn2tb : nat * nat -> N * N

tn2tb is not universe polymorphic
Arguments tn2tb t
tn2tb is transparent
Expands to: Constant prosa.implementation.refinements.refinements.tn2tb
Declared in library prosa.implementation.refinements.refinements, line 43, characters 11-16
tn2tb
     : nat * nat -> N * N
```

Body:

```coq
tn2tb = [eta @tmap nat N bin_of_nat]
     : nat * nat -> N * N

Arguments tn2tb t
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.tn2tb : ℕ × ℕ →
  Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.tn2tb : ℕ × ℕ →
  Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N :=
fun t => Prosa.Implementation.Refinements.Refinements.tmap Prosa.Implementation.Refinements.Refinements.bin_of_nat t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_tn2tb
     : Prod_inst3 Nat Nat ->
       Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_tn2tb@{} =
fun t : Prod_inst3 Nat Nat =>
Prosa_Implementation_Refinements_Refinements_tmap Nat Prosa_Implementation_Refinements_Refinements_N
  Prosa_Implementation_Refinements_Refinements_bin_of_nat t
     : Prod_inst3 Nat Nat ->
       Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_Refinements_tn2tb t
```
