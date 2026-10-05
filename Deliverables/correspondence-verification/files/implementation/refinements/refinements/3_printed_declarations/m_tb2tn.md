# `m_tb2tn`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.m_tb2tn`
- Lean: `Prosa.Implementation.Refinements.Refinements.m_tb2tn`
- Certificate: `m_tb2tn_correspondence`

## Official Rocq

```coq
m_tb2tn : seq (N * N) -> seq (nat * nat)

m_tb2tn is not universe polymorphic
Arguments m_tb2tn xs%_seq_scope
m_tb2tn is transparent
Expands to: Constant prosa.implementation.refinements.refinements.m_tb2tn
Declared in library prosa.implementation.refinements.refinements, line 44, characters 11-18
m_tb2tn
     : seq (N * N) -> seq (nat * nat)
```

Body:

```coq
m_tb2tn = [eta @map (N * N) (nat * nat) tb2tn]
     : seq (N * N) -> seq (nat * nat)

Arguments m_tb2tn xs%_seq_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.m_tb2tn : List
    (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N) →
  List (ℕ × ℕ)
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.m_tb2tn : List
    (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N) →
  List (ℕ × ℕ) :=
fun xs => List.map Prosa.Implementation.Refinements.Refinements.tb2tn xs
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_m_tb2tn
     : List_inst1
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N) ->
       List_inst1 (Prod_inst3 Nat Nat)
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_m_tb2tn@{} =
fun
  xs : List_inst1
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N) =>
List_map_inst3
  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_N)
  (Prod_inst3 Nat Nat) Prosa_Implementation_Refinements_Refinements_tb2tn xs
     : List_inst1
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N) ->
       List_inst1 (Prod_inst3 Nat Nat)

Arguments Prosa_Implementation_Refinements_Refinements_m_tb2tn xs
```
