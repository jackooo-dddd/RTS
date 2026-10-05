# `refine_task_deadline`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.task.refine_task_deadline`
- Lean: `Prosa.Implementation.Refinements.Task.refine_task_deadline`
- Certificate: `refine_task_deadline_correspondence`

## Official Rocq

```coq
refine_task_deadline :
@refines (Equality.sort Task -> nat) (@task_T binnat.N -> binnat.N) (Rtask ==> Rnat) task_deadline
  (@task_deadline_T binnat.N)

refine_task_deadline is not universe polymorphic
refine_task_deadline is opaque
Expands to: Constant prosa.implementation.refinements.task.refine_task_deadline
Declared in library prosa.implementation.refinements.task, line 175, characters 18-38
refine_task_deadline
     : @refines (Equality.sort Task -> nat) (@task_T binnat.N -> binnat.N) (Rtask ==> Rnat) task_deadline
         (@task_deadline_T binnat.N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.refine_task_deadline : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    Prosa.Implementation.Refinements.Refinements.Rnat)
  Prosa.Implementation.Definitions.Task.concrete_task.task_deadline
  Prosa.Implementation.Refinements.Task.task_T.task_deadline_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_refine_task_deadline
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task -> Nat)
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) Nat
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Task_Rtask
            Prosa_Implementation_Refinements_Refinements_Rnat)
         Prosa_Implementation_Definitions_Task_concrete_task_task_deadline
         (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T
            Prosa_Implementation_Refinements_Refinements_N)
```
