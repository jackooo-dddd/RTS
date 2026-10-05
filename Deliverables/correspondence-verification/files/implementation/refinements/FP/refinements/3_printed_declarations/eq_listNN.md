# `eq_listNN`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.eq_listNN`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.eq_listNN`
- Certificate: `eq_listNN_correspondence`

## Official Rocq

```coq
eq_listNN : eq_of (seq (N * N))

eq_listNN is not universe polymorphic
eq_listNN is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.eq_listNN
Declared in library prosa.implementation.refinements.FP.refinements, line 154, characters 16-25
eq_listNN
     : eq_of (seq (N * N))
```

Body:

```coq
eq_listNN =
fun x : seq (N * N) =>
       (Datatypes_list__canonical__eqtype_Equality
          (Datatypes_prod__canonical__eqtype_Equality BinNums_N__canonical__eqtype_Equality
             BinNums_N__canonical__eqtype_Equality))
       x]
     : eq_of (seq (N * N))
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.eq_listNN : Prosa.Implementation.Refinements.Refinements.eq_of
  (List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N))
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Refinements.FP.Refinements.eq_listNN : Prosa.Implementation.Refinements.Refinements.eq_of
  (List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N)) :=
{ eq_op := fun x y => decide (x = y) }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_eq_listNN
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N))
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_eq_listNN@{} =
Prosa_Implementation_Refinements_Refinements_eq_of_mk
  (List_inst1
     (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
        Prosa_Implementation_Refinements_Refinements_N))
  (fun
     x
      y : List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N) =>
   Decidable_decide
     (@eq
        (List_inst1
           (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
              Prosa_Implementation_Refinements_Refinements_N))
        x y)
     (instDecidableEqList_inst1
        (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
           Prosa_Implementation_Refinements_Refinements_N)
        (fun
           a
            b : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N =>
         instDecidableEqProd_inst3 Prosa_Implementation_Refinements_Refinements_N
           Prosa_Implementation_Refinements_Refinements_N
           Prosa_Implementation_Refinements_ArrivalBound_instDecidableEqN
           Prosa_Implementation_Refinements_ArrivalBound_instDecidableEqN a b)
        x y))
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N))
```
