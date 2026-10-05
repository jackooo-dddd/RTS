# `m_b2n`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.m_b2n`
- Lean: `Prosa.Implementation.Refinements.Refinements.m_b2n`
- Certificate: `m_b2n_correspondence`

## Official Rocq

```coq
m_b2n : seq N -> seq nat

m_b2n is not universe polymorphic
Arguments m_b2n b%_seq_scope
m_b2n is transparent
Expands to: Constant prosa.implementation.refinements.refinements.m_b2n
Declared in library prosa.implementation.refinements.refinements, line 37, characters 11-16
m_b2n
     : seq N -> seq nat
```

Body:

```coq
m_b2n = [eta @map N nat nat_of_bin]
     : seq N -> seq nat

Arguments m_b2n b%_seq_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.m_b2n : List Prosa.Implementation.Refinements.Refinements.N → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.m_b2n : List Prosa.Implementation.Refinements.Refinements.N → List ℕ :=
fun b => List.map Prosa.Implementation.Refinements.Refinements.nat_of_bin b
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_m_b2n
     : List_inst1 Prosa_Implementation_Refinements_Refinements_N -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_m_b2n@{} =
fun b : List_inst1 Prosa_Implementation_Refinements_Refinements_N =>
List_map_inst3 Prosa_Implementation_Refinements_Refinements_N Nat
  Prosa_Implementation_Refinements_Refinements_nat_of_bin b
     : List_inst1 Prosa_Implementation_Refinements_Refinements_N -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_Refinements_m_b2n b
```
