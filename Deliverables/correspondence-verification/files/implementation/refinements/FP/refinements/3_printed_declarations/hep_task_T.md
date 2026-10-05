# `hep_task_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.refinements.hep_task_T`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.hep_task_T`
- Certificate: `hep_task_T_correspondence`

## Official Rocq

```coq
hep_task_T : forall {T : Type}, leq_of T -> @task_T T -> @task_T T -> bool

hep_task_T is not universe polymorphic
Arguments hep_task_T {T}%_type_scope {leq_of0} tsk_o tsk
hep_task_T is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.hep_task_T
Declared in library prosa.implementation.refinements.FP.refinements, line 21, characters 13-23
@hep_task_T
     : forall T : Type, leq_of T -> @task_T T -> @task_T T -> bool
```

Body:

```coq
hep_task_T =
fun (T : Type) (leq_of0 : leq_of T) (tsk_o tsk : @task_T T) =>
(@task_priority_T T tsk <= @task_priority_T T tsk_o)%C
     : forall {T : Type}, leq_of T -> @task_T T -> @task_T T -> bool

Arguments hep_task_T {T}%_type_scope {leq_of0} tsk_o tsk
```

## Lean

```lean
@Prosa.Implementation.Refinements.FP.Refinements.hep_task_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.leq_of T] →
    Prosa.Implementation.Refinements.Task.task_T T → Prosa.Implementation.Refinements.Task.task_T T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.Refinements.hep_task_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.leq_of T] →
    Prosa.Implementation.Refinements.Task.task_T T → Prosa.Implementation.Refinements.Task.task_T T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.leq_of T] tsk_o tsk =>
  Prosa.Implementation.Refinements.Refinements.leq_op tsk.task_priority_T tsk_o.task_priority_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_hep_task_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Task_task_T T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_hep_task_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (tsk_o tsk : Prosa_Implementation_Refinements_Task_task_T T) =>
Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
  inst_3
  (Prosa_Implementation_Refinements_Task_task_T_task_priority_T T tsk)
  (Prosa_Implementation_Refinements_Task_task_T_task_priority_T T tsk_o)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Task_task_T T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Bool

Arguments Prosa_Implementation_Refinements_FP_Refinements_hep_task_T T%_type_scope
  inst_3 
  tsk_o tsk
```
