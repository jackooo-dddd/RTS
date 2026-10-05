# `eq_listN`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.eq_listN`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.eq_listN`
- Certificate: `eq_listN_correspondence`

## Official Rocq

```coq
eq_listN : eq_of (seq N)

eq_listN is not universe polymorphic
eq_listN is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.eq_listN
Declared in library prosa.implementation.refinements.FP.refinements, line 153, characters 16-24
eq_listN
     : eq_of (seq N)
```

Body:

```coq
eq_listN =
fun x : seq N =>
     : eq_of (seq N)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.eq_listN : Prosa.Implementation.Refinements.Refinements.eq_of
  (List Prosa.Implementation.Refinements.Refinements.N)
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Refinements.FP.Refinements.eq_listN : Prosa.Implementation.Refinements.Refinements.eq_of
  (List Prosa.Implementation.Refinements.Refinements.N) :=
{ eq_op := fun x y => decide (x = y) }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_eq_listN
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_eq_listN@{} =
Prosa_Implementation_Refinements_Refinements_eq_of_mk
  (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
  (fun x y : List_inst1 Prosa_Implementation_Refinements_Refinements_N =>
   Decidable_decide (@eq (List_inst1 Prosa_Implementation_Refinements_Refinements_N) x y)
     (instDecidableEqList_inst1 Prosa_Implementation_Refinements_Refinements_N
        Prosa_Implementation_Refinements_ArrivalBound_instDecidableEqN x y))
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
```
