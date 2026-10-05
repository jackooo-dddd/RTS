# `refine_task_cost`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.task.refine_task_cost`
- Lean: `Prosa.Implementation.Refinements.Task.refine_task_cost`
- Certificate: `refine_task_cost_correspondence`

## Official Rocq

```coq
refine_task_cost :
@refines (Equality.sort Task -> nat) (@task_T binnat.N -> binnat.N) (Rtask ==> Rnat) task_cost
  (@task_cost_T binnat.N)

refine_task_cost is not universe polymorphic
refine_task_cost is opaque
Expands to: Constant prosa.implementation.refinements.task.refine_task_cost
Declared in library prosa.implementation.refinements.task, line 159, characters 18-34
refine_task_cost
     : @refines (Equality.sort Task -> nat) (@task_T binnat.N -> binnat.N) (Rtask ==> Rnat) task_cost
         (@task_cost_T binnat.N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.refine_task_cost : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    Prosa.Implementation.Refinements.Refinements.Rnat)
  Prosa.Implementation.Definitions.Task.concrete_task.task_cost Prosa.Implementation.Refinements.Task.task_T.task_cost_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_refine_task_cost
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task -> Nat)
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) Nat
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Task_Rtask
            Prosa_Implementation_Refinements_Refinements_Rnat)
         Prosa_Implementation_Definitions_Task_concrete_task_task_cost
         (Prosa_Implementation_Refinements_Task_task_T_task_cost_T
            Prosa_Implementation_Refinements_Refinements_N)
```
