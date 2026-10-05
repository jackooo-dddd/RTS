# `refine_shift_points_neg`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_shift_points_neg`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_shift_points_neg`
- Certificate: `refine_shift_points_neg_correspondence`

## Official Rocq

```coq
refine_shift_points_neg :
@refines (seq nat -> nat -> seq nat) (seq N -> N -> seq N)
  (@list_R nat N Rnat ==> Rnat ==> @list_R nat N Rnat) shift_points_neg (@shift_points_neg_T N sub_N leq_N)

refine_shift_points_neg is not universe polymorphic
refine_shift_points_neg is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_shift_points_neg
Declared in library prosa.implementation.refinements.refinements, line 380, characters 16-39
refine_shift_points_neg
     : @refines (seq nat -> nat -> seq nat) (seq N -> N -> seq N)
         (@list_R nat N Rnat ==> Rnat ==> @list_R nat N Rnat) shift_points_neg
         (@shift_points_neg_T N sub_N leq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_shift_points_neg : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)))
  Prosa.Util.List.shift_points_neg Prosa.Implementation.Refinements.Refinements.shift_points_neg_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_shift_points_neg
     : Prosa_Implementation_Refinements_Refinements_refines (List_inst1 Nat -> Nat -> List_inst1 Nat)
         (List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N ->
          List_inst1 Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 Nat)
            (List_inst1 Prosa_Implementation_Refinements_Refinements_N) (Nat -> List_inst1 Nat)
            (Prosa_Implementation_Refinements_Refinements_N ->
             List_inst1 Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_Refinements_list_R Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat)
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N (List_inst1 Nat)
               (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Refinements_Rnat
               (Prosa_Implementation_Refinements_Refinements_list_R Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat)))
         Prosa_Util_List_shift_points_neg
         (Prosa_Implementation_Refinements_Refinements_shift_points_neg_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_sub_N
            Prosa_Implementation_Refinements_Refinements_leq_N)
```
