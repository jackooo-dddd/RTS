# `refine_task_id`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.task.refine_task_id`
- Lean: `Prosa.Implementation.Refinements.Task.refine_task_id`
- Certificate: `refine_task_id_correspondence`

## Official Rocq

```coq
refine_task_id :
@refines (Equality.sort Task -> nat) (@task_T binnat.N -> binnat.N) (Rtask ==> Rnat) task_id
  (@task_id_T binnat.N)

refine_task_id is not universe polymorphic
refine_task_id is opaque
Expands to: Constant prosa.implementation.refinements.task.refine_task_id
Declared in library prosa.implementation.refinements.task, line 151, characters 18-32
refine_task_id
     : @refines (Equality.sort Task -> nat) (@task_T binnat.N -> binnat.N) (Rtask ==> Rnat) task_id
         (@task_id_T binnat.N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.refine_task_id : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    Prosa.Implementation.Refinements.Refinements.Rnat)
  Prosa.Implementation.Definitions.Task.concrete_task.task_id Prosa.Implementation.Refinements.Task.task_T.task_id_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_refine_task_id
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task -> Nat)
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) Nat
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Task_Rtask
            Prosa_Implementation_Refinements_Refinements_Rnat)
         Prosa_Implementation_Definitions_Task_concrete_task_task_id
         (Prosa_Implementation_Refinements_Task_task_T_task_id_T
            Prosa_Implementation_Refinements_Refinements_N)
```
