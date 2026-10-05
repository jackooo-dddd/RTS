# `m_n2b`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.m_n2b`
- Lean: `Prosa.Implementation.Refinements.Refinements.m_n2b`
- Certificate: `m_n2b_correspondence`

## Official Rocq

```coq
m_n2b : seq nat -> seq N

m_n2b is not universe polymorphic
Arguments m_n2b n%_seq_scope
m_n2b is transparent
Expands to: Constant prosa.implementation.refinements.refinements.m_n2b
Declared in library prosa.implementation.refinements.refinements, line 38, characters 11-16
m_n2b
     : seq nat -> seq N
```

Body:

```coq
m_n2b = [eta @map nat N bin_of_nat]
     : seq nat -> seq N

Arguments m_n2b n%_seq_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.m_n2b : List ℕ → List Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.m_n2b : List ℕ → List Prosa.Implementation.Refinements.Refinements.N :=
fun n => List.map Prosa.Implementation.Refinements.Refinements.bin_of_nat n
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_m_n2b
     : List_inst1 Nat -> List_inst1 Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_m_n2b@{} =
fun n : List_inst1 Nat =>
List_map_inst3 Nat Prosa_Implementation_Refinements_Refinements_N
  Prosa_Implementation_Refinements_Refinements_bin_of_nat n
     : List_inst1 Nat -> List_inst1 Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_Refinements_m_n2b n
```
