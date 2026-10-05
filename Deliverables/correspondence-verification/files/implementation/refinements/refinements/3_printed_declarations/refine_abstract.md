# `refine_abstract`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_abstract`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_abstract`
- Certificate: `refine_abstract_correspondence`

## Official Rocq

```coq
refine_abstract :
forall xs : seq N, @refines (seq nat) (seq N) (@list_R nat N Rnat) [seq nat_of_bin i | i <- xs] xs

refine_abstract is not universe polymorphic
Arguments refine_abstract xs%_seq_scope
refine_abstract is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_abstract
Declared in library prosa.implementation.refinements.refinements, line 394, characters 16-31
refine_abstract
     : forall xs : seq N, @refines (seq nat) (seq N) (@list_R nat N Rnat) [seq nat_of_bin i | i <- xs] xs
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_abstract : (xs :
    List Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Refinements.refines
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)
    (List.map Prosa.Implementation.Refinements.Refinements.nat_of_bin xs) xs
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_abstract
     : forall xs : List_inst1 Prosa_Implementation_Refinements_Refinements_N,
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 Nat)
         (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_list_R Nat
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_Rnat)
         (List_map_inst3 Prosa_Implementation_Refinements_Refinements_N Nat
            Prosa_Implementation_Refinements_Refinements_nat_of_bin xs)
         xs
```
