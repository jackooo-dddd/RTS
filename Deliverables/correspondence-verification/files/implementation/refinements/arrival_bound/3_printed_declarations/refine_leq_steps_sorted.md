# `refine_leq_steps_sorted`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_bound.refine_leq_steps_sorted`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.refine_leq_steps_sorted`
- Certificate: `refine_leq_steps_sorted_correspondence`

## Official Rocq

```coq
refine_leq_steps_sorted :
forall (xs : seq (nat * nat)) (xs' : seq (N * N)),
@refines (seq (nat * nat)) (seq (N * N)) (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat)) xs xs' ->
@refines bool bool bool_R (@sorted (nat * nat) leq_steps xs) (@sorted (N * N) (@leq_steps_T N leq_N) xs')

refine_leq_steps_sorted is not universe polymorphic
Arguments refine_leq_steps_sorted (xs xs')%_seq_scope _
refine_leq_steps_sorted is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.refine_leq_steps_sorted
Declared in library prosa.implementation.refinements.arrival_bound, line 233, characters 18-41
refine_leq_steps_sorted
     : forall (xs : seq (nat * nat)) (xs' : seq (N * N)),
       @refines (seq (nat * nat)) (seq (N * N)) (@list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat))
         xs xs' ->
       @refines bool bool bool_R (@sorted (nat * nat) leq_steps xs)
         (@sorted (N * N) (@leq_steps_T N leq_N) xs')
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.refine_leq_steps_sorted : (xs : List (ℕ × ℕ)) →
  (xs' : List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N)) →
    Prosa.Implementation.Refinements.Refinements.refines
        (Prosa.Implementation.Refinements.Refinements.list_R
          (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
            Prosa.Implementation.Refinements.Refinements.Rnat))
        xs xs' →
      Prosa.Implementation.Refinements.Refinements.refines Prosa.Implementation.Refinements.Refinements.bool_R
        (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sortedBool
          Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.leq_steps xs)
        (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sortedBool
          Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T xs')
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_refine_leq_steps_sorted
     : forall (xs : List_inst1 (Prod_inst3 Nat Nat))
         (xs' : List_inst1
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N)),
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 (Prod_inst3 Nat Nat))
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N))
         (Prosa_Implementation_Refinements_Refinements_list_R (Prod_inst3 Nat Nat)
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_Refinements_prod_R Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat))
         xs xs' ->
       Prosa_Implementation_Refinements_Refinements_refines Bool Bool
         Prosa_Implementation_Refinements_Refinements_bool_R
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1
            (Prod_inst3 Prosa_Behavior_Time_duration Nat)
            Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps xs)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_leq_N)
            xs')
```
