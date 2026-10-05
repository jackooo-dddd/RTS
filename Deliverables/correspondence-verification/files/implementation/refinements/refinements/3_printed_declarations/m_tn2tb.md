# `m_tn2tb`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.m_tn2tb`
- Lean: `Prosa.Implementation.Refinements.Refinements.m_tn2tb`
- Certificate: `m_tn2tb_correspondence`

## Official Rocq

```coq
m_tn2tb : seq (nat * nat) -> seq (N * N)

m_tn2tb is not universe polymorphic
Arguments m_tn2tb xs%_seq_scope
m_tn2tb is transparent
Expands to: Constant prosa.implementation.refinements.refinements.m_tn2tb
Declared in library prosa.implementation.refinements.refinements, line 45, characters 11-18
m_tn2tb
     : seq (nat * nat) -> seq (N * N)
```

Body:

```coq
m_tn2tb = [eta @map (nat * nat) (N * N) tn2tb]
     : seq (nat * nat) -> seq (N * N)

Arguments m_tn2tb xs%_seq_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.m_tn2tb : List (ℕ × ℕ) →
  List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N)
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.m_tn2tb : List (ℕ × ℕ) →
  List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N) :=
fun xs => List.map Prosa.Implementation.Refinements.Refinements.tn2tb xs
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_m_tn2tb
     : List_inst1 (Prod_inst3 Nat Nat) ->
       List_inst1
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N)
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_m_tn2tb@{} =
fun xs : List_inst1 (Prod_inst3 Nat Nat) =>
List_map_inst3 (Prod_inst3 Nat Nat)
  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_N)
  Prosa_Implementation_Refinements_Refinements_tn2tb xs
     : List_inst1 (Prod_inst3 Nat Nat) ->
       List_inst1
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N)

Arguments Prosa_Implementation_Refinements_Refinements_m_tn2tb xs
```
