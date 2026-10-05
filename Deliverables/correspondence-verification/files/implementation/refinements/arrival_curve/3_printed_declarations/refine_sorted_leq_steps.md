# `refine_sorted_leq_steps`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_curve.refine_sorted_leq_steps`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.refine_sorted_leq_steps`
- Certificate: `refine_sorted_leq_steps_correspondence`

## Official Rocq

```coq
refine_sorted_leq_steps :
forall tsk : @task_T binnat.N,
@refines bool bool bool_R
  (@sorted (nat * nat) leq_steps (steps_of (get_arrival_curve_prefix (taskT_to_task tsk))))
  (@sorted (binnat.N * binnat.N) (@leq_steps_T binnat.N leq_N)
     (@get_extrapolated_arrival_curve_T binnat.N one_N tsk).2)

refine_sorted_leq_steps is not universe polymorphic
Arguments refine_sorted_leq_steps tsk
refine_sorted_leq_steps is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.refine_sorted_leq_steps
Declared in library prosa.implementation.refinements.arrival_curve, line 357, characters 18-41
refine_sorted_leq_steps
     : forall tsk : @task_T binnat.N,
       @refines bool bool bool_R
         (@sorted (nat * nat) leq_steps (steps_of (get_arrival_curve_prefix (taskT_to_task tsk))))
         (@sorted (binnat.N * binnat.N) (@leq_steps_T binnat.N leq_N)
            (@get_extrapolated_arrival_curve_T binnat.N one_N tsk).2)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.refine_sorted_leq_steps : (tsk :
    Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Refinements.refines Prosa.Implementation.Refinements.Refinements.bool_R
    (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sortedBool
      Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.leq_steps
      (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of
        (Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix
          (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))))
    (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sortedBool
      Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T
      (Prosa.Implementation.Refinements.Task.get_extrapolated_arrival_curve_T tsk).2)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_refine_sorted_leq_steps
     : forall
         tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N,
       Prosa_Implementation_Refinements_Refinements_refines Bool Bool
         Prosa_Implementation_Refinements_Refinements_bool_R
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1
            (Prod_inst3 Prosa_Behavior_Time_duration Nat)
            Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps
            (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of
               (Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix
                  (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))))
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_leq_N)
            (Prod_snd_inst3 Prosa_Implementation_Refinements_Refinements_N
               (List_inst1
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N))
               (Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_one_N tsk)))
```
