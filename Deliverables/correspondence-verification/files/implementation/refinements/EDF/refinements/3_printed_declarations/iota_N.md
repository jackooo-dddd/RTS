# `iota_N`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.refinements.iota_N`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.iota_N`
- Certificate: `iota_N_correspondence`

## Official Rocq

```coq
iota_N : N -> N -> seq N

iota_N is not universe polymorphic
Arguments iota_N (a Δ)%_N_scope
iota_N is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.iota_N
Declared in library prosa.implementation.refinements.EDF.refinements, line 62, characters 11-17
iota_N
     : N -> N -> seq N
```

Body:

```coq
iota_N = fun a Δ : N => @iota_T N one_N add_N a (nat_of_bin Δ)
     : N -> N -> seq N

Arguments iota_N (a Δ)%_N_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.iota_N : Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.Refinements.iota_N : Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N :=
fun a Δ =>
  Prosa.Implementation.Refinements.Refinements.iota_T a (Prosa.Implementation.Refinements.Refinements.nat_of_bin Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_iota_N
     : Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_iota_N@{} =
fun a _UU0394_ : Prosa_Implementation_Refinements_Refinements_N =>
Prosa_Implementation_Refinements_Refinements_iota_T Prosa_Implementation_Refinements_Refinements_N
  Prosa_Implementation_Refinements_Refinements_one_N Prosa_Implementation_Refinements_Refinements_add_N a
  (Prosa_Implementation_Refinements_Refinements_nat_of_bin _UU0394_)
     : Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_EDF_Refinements_iota_N a _UU0394_
```
