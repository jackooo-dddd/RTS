# `eq_NlistNN`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_bound.eq_NlistNN`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.eq_NlistNN`
- Certificate: `eq_NlistNN_correspondence`

## Official Rocq

```coq
eq_NlistNN : eq_of (N * seq (N * N))

eq_NlistNN is not universe polymorphic
eq_NlistNN is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.eq_NlistNN
Declared in library prosa.implementation.refinements.arrival_bound, line 311, characters 18-28
eq_NlistNN
     : eq_of (N * seq (N * N))
```

Body:

```coq
eq_NlistNN =
fun x : N * seq (N * N) =>
       (Datatypes_prod__canonical__eqtype_Equality BinNums_N__canonical__eqtype_Equality
          (Datatypes_list__canonical__eqtype_Equality
             (Datatypes_prod__canonical__eqtype_Equality BinNums_N__canonical__eqtype_Equality
                BinNums_N__canonical__eqtype_Equality)))
       x]
     : eq_of (N * seq (N * N))
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.eq_NlistNN : Prosa.Implementation.Refinements.Refinements.eq_of
  (Prosa.Implementation.Refinements.Refinements.N ×
    List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N))
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Refinements.ArrivalBound.eq_NlistNN : Prosa.Implementation.Refinements.Refinements.eq_of
  (Prosa.Implementation.Refinements.Refinements.N ×
    List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N)) :=
{ eq_op := fun x y => decide (x = y) }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_eq_NlistNN
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)))
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_eq_NlistNN@{} =
Prosa_Implementation_Refinements_Refinements_eq_of_mk
  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
     (List_inst1
        (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
           Prosa_Implementation_Refinements_Refinements_N)))
  (fun
     x
      y : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)) =>
   Decidable_decide
     (@eq
        (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
           (List_inst1
              (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                 Prosa_Implementation_Refinements_Refinements_N)))
        x y)
     (instDecidableEqProd_inst3 Prosa_Implementation_Refinements_Refinements_N
        (List_inst1
           (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
              Prosa_Implementation_Refinements_Refinements_N))
        Prosa_Implementation_Refinements_ArrivalBound_instDecidableEqN
        (fun
           a
            b : List_inst1
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N) =>
         instDecidableEqList_inst1
           (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
              Prosa_Implementation_Refinements_Refinements_N)
           (fun
              a0
               b0 : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                      Prosa_Implementation_Refinements_Refinements_N =>
            instDecidableEqProd_inst3 Prosa_Implementation_Refinements_Refinements_N
              Prosa_Implementation_Refinements_Refinements_N
              Prosa_Implementation_Refinements_ArrivalBound_instDecidableEqN
              Prosa_Implementation_Refinements_ArrivalBound_instDecidableEqN a0 b0)
           a b)
        x y))
     : Prosa_Implementation_Refinements_Refinements_eq_of
         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            (List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N)))
```
