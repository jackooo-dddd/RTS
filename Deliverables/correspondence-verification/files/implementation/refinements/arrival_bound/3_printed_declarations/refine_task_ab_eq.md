# `refine_task_ab_eq`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_bound.refine_task_ab_eq`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.refine_task_ab_eq`
- Certificate: `refine_task_ab_eq_correspondence`

## Official Rocq

```coq
refine_task_ab_eq :
@refines (task_arrivals_bound -> task_arrivals_bound -> bool)
  (@task_arrivals_bound_T N -> @task_arrivals_bound_T N -> bool) (Rtask_ab ==> Rtask_ab ==> bool_R)
  (@eq_op arrival_bound_task_arrivals_bound__canonical__eqtype_Equality) eq_taskab

refine_task_ab_eq is not universe polymorphic
refine_task_ab_eq is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.refine_task_ab_eq
Declared in library prosa.implementation.refinements.arrival_bound, line 315, characters 18-35
refine_task_ab_eq
     : @refines (task_arrivals_bound -> task_arrivals_bound -> bool)
         (@task_arrivals_bound_T N -> @task_arrivals_bound_T N -> bool) (Rtask_ab ==> Rtask_ab ==> bool_R)
         (@eq_op arrival_bound_task_arrivals_bound__canonical__eqtype_Equality) eq_taskab
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.refine_task_ab_eq : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab
      Prosa.Implementation.Refinements.Refinements.bool_R))
  (fun x y => decide (x = y)) Prosa.Implementation.Refinements.Refinements.eq_op
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_refine_task_ab_eq
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
          Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound -> Bool)
         (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
            Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
            Prosa_Implementation_Refinements_Refinements_N ->
          Bool)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
            (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
               Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound -> Bool)
            (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
               Prosa_Implementation_Refinements_Refinements_N ->
             Bool)
            Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab
            (Prosa_Implementation_Refinements_Refinements_hrespectful
               Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
               (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
                  Prosa_Implementation_Refinements_Refinements_N)
               Bool Bool Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab
               Prosa_Implementation_Refinements_Refinements_bool_R))
         (fun x y : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound =>
          Decidable_decide (@eq Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound x y)
            (Prosa_Implementation_Definitions_ArrivalBound_instDecidableEqTask_arrivals_bound x y))
         (Prosa_Implementation_Refinements_Refinements_eq_of_eq_op
            (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
               Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_ArrivalBound_eq_taskab)
```
