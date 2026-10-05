# `refine_repeat_steps_with_offset`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_curve.refine_repeat_steps_with_offset`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.refine_repeat_steps_with_offset`
- Certificate: `refine_repeat_steps_with_offset_correspondence`

## Official Rocq

```coq
refine_repeat_steps_with_offset :
@refines (Equality.sort Task -> seq nat -> seq nat) (@task_T binnat.N -> seq binnat.N -> seq binnat.N)
  (Rtask ==> @list_R nat binnat.N Rnat ==> @list_R nat binnat.N Rnat) repeat_steps_with_offset
  (@repeat_steps_with_offset_T binnat.N one_N add_N)

refine_repeat_steps_with_offset is not universe polymorphic
refine_repeat_steps_with_offset is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.refine_repeat_steps_with_offset
Declared in library prosa.implementation.refinements.arrival_curve, line 189, characters 18-49
refine_repeat_steps_with_offset
     : @refines (Equality.sort Task -> seq nat -> seq nat) (@task_T binnat.N -> seq binnat.N -> seq binnat.N)
         (Rtask ==> @list_R nat binnat.N Rnat ==> @list_R nat binnat.N Rnat) repeat_steps_with_offset
         (@repeat_steps_with_offset_T binnat.N one_N add_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.refine_repeat_steps_with_offset : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    (Prosa.Implementation.Refinements.Refinements.hrespectful
      (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)
      (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)))
  Prosa.Implementation.Refinements.ArrivalCurve.repeat_steps_with_offset
  Prosa.Implementation.Refinements.Task.repeat_steps_with_offset_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_refine_repeat_steps_with_offset
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task -> List_inst1 Nat -> List_inst1 Nat)
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
          List_inst1 Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
            (List_inst1 Nat -> List_inst1 Nat)
            (List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
             List_inst1 Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_Task_Rtask
            (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 Nat)
               (List_inst1 Prosa_Implementation_Refinements_Refinements_N) (List_inst1 Nat)
               (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
               (Prosa_Implementation_Refinements_Refinements_list_R Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat)
               (Prosa_Implementation_Refinements_Refinements_list_R Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat)))
         Prosa_Implementation_Refinements_ArrivalCurve_repeat_steps_with_offset
         (Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N)
```
