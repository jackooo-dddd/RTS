# `task_eqdef`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.task.task_eqdef`
- Lean: `Prosa.Implementation.Definitions.Task.task_eqdef`
- Certificate: `task_eqdef_correspondence`

## Official Rocq

```coq
task_eqdef : concrete_task -> concrete_task -> bool

task_eqdef is not universe polymorphic
Arguments task_eqdef t1 t2
task_eqdef is transparent
Expands to: Constant prosa.implementation.definitions.task.task_eqdef
Declared in library prosa.implementation.definitions.task, line 30, characters 11-21
task_eqdef
     : concrete_task -> concrete_task -> bool
```

Body:

```coq
task_eqdef =
fun t1 t2 : concrete_task =>
(task_id t1 == task_id t2) && (task_cost t1 == task_cost t2) && (task_arrival t1 == task_arrival t2) &&
(task_deadline t1 == task_deadline t2) && (task_priority t1 == task_priority t2)
     : concrete_task -> concrete_task -> bool

Arguments task_eqdef t1 t2
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.task_eqdef : Prosa.Implementation.Definitions.Task.concrete_task →
  Prosa.Implementation.Definitions.Task.concrete_task → Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.Task.task_eqdef : Prosa.Implementation.Definitions.Task.concrete_task →
  Prosa.Implementation.Definitions.Task.concrete_task → Bool :=
fun t1 t2 =>
  decide (t1.task_id = t2.task_id) && decide (t1.task_cost = t2.task_cost) &&
        decide (t1.task_arrival = t2.task_arrival) &&
      decide (t1.task_deadline = t2.task_deadline) &&
    decide (t1.task_priority = t2.task_priority)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_task_eqdef
     : Prosa_Implementation_Definitions_Task_concrete_task ->
       Prosa_Implementation_Definitions_Task_concrete_task -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_Task_task_eqdef@{} =
fun t1 t2 : Prosa_Implementation_Definitions_Task_concrete_task =>
Bool_and
  (Bool_and
     (Bool_and
        (Bool_and
           (Decidable_decide
              (@eq Nat (Prosa_Implementation_Definitions_Task_concrete_task_task_id t1)
                 (Prosa_Implementation_Definitions_Task_concrete_task_task_id t2))
              (instDecidableEqNat (Prosa_Implementation_Definitions_Task_concrete_task_task_id t1)
                 (Prosa_Implementation_Definitions_Task_concrete_task_task_id t2)))
           (Decidable_decide
              (@eq Nat (Prosa_Implementation_Definitions_Task_concrete_task_task_cost t1)
                 (Prosa_Implementation_Definitions_Task_concrete_task_task_cost t2))
              (instDecidableEqNat (Prosa_Implementation_Definitions_Task_concrete_task_task_cost t1)
                 (Prosa_Implementation_Definitions_Task_concrete_task_task_cost t2))))
        (Decidable_decide
           (@eq Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
              (Prosa_Implementation_Definitions_Task_concrete_task_task_arrival t1)
              (Prosa_Implementation_Definitions_Task_concrete_task_task_arrival t2))
           (Prosa_Implementation_Definitions_ArrivalBound_instDecidableEqTask_arrivals_bound
              (Prosa_Implementation_Definitions_Task_concrete_task_task_arrival t1)
              (Prosa_Implementation_Definitions_Task_concrete_task_task_arrival t2))))
     (Decidable_decide
        (@eq Prosa_Behavior_Time_instant
           (Prosa_Implementation_Definitions_Task_concrete_task_task_deadline t1)
           (Prosa_Implementation_Definitions_Task_concrete_task_task_deadline t2))
        (instDecidableEqNat (Prosa_Implementation_Definitions_Task_concrete_task_task_deadline t1)
           (Prosa_Implementation_Definitions_Task_concrete_task_task_deadline t2))))
  (Decidable_decide
     (@eq Nat (Prosa_Implementation_Definitions_Task_concrete_task_task_priority t1)
        (Prosa_Implementation_Definitions_Task_concrete_task_task_priority t2))
     (instDecidableEqNat (Prosa_Implementation_Definitions_Task_concrete_task_task_priority t1)
        (Prosa_Implementation_Definitions_Task_concrete_task_task_priority t2)))
     : Prosa_Implementation_Definitions_Task_concrete_task ->
       Prosa_Implementation_Definitions_Task_concrete_task -> Bool

Arguments Prosa_Implementation_Definitions_Task_task_eqdef t1 t2
```
