# `job_eqdef`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.task.job_eqdef`
- Lean: `Prosa.Implementation.Definitions.Task.job_eqdef`
- Certificate: `job_eqdef_correspondence`

## Official Rocq

```coq
job_eqdef : concrete_job -> concrete_job -> bool

job_eqdef is not universe polymorphic
Arguments job_eqdef j1 j2
job_eqdef is transparent
Expands to: Constant prosa.implementation.definitions.task.job_eqdef
Declared in library prosa.implementation.definitions.task, line 90, characters 11-20
job_eqdef
     : concrete_job -> concrete_job -> bool
```

Body:

```coq
job_eqdef =
fun j1 j2 : concrete_job =>
(job_id j1 == job_id j2) && (job_arrival j1 == job_arrival j2) && (job_cost j1 == job_cost j2) &&
(job_deadline j1 == job_deadline j2) && (job_task j1 == job_task j2)
     : concrete_job -> concrete_job -> bool

Arguments job_eqdef j1 j2
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.job_eqdef : Prosa.Implementation.Definitions.Task.concrete_job →
  Prosa.Implementation.Definitions.Task.concrete_job → Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.Task.job_eqdef : Prosa.Implementation.Definitions.Task.concrete_job →
  Prosa.Implementation.Definitions.Task.concrete_job → Bool :=
fun j1 j2 =>
  decide (j1.job_id = j2.job_id) && decide (j1.job_arrival = j2.job_arrival) && decide (j1.job_cost = j2.job_cost) &&
      decide (j1.job_deadline = j2.job_deadline) &&
    decide (j1.job_task = j2.job_task)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_job_eqdef
     : Prosa_Implementation_Definitions_Task_concrete_job ->
       Prosa_Implementation_Definitions_Task_concrete_job -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_Task_job_eqdef@{} =
fun j1 j2 : Prosa_Implementation_Definitions_Task_concrete_job =>
Bool_and
  (Bool_and
     (Bool_and
        (Bool_and
           (Decidable_decide
              (@eq Nat (Prosa_Implementation_Definitions_Task_concrete_job_job_id j1)
                 (Prosa_Implementation_Definitions_Task_concrete_job_job_id j2))
              (instDecidableEqNat (Prosa_Implementation_Definitions_Task_concrete_job_job_id j1)
                 (Prosa_Implementation_Definitions_Task_concrete_job_job_id j2)))
           (Decidable_decide
              (@eq Prosa_Behavior_Time_instant
                 (Prosa_Implementation_Definitions_Task_concrete_job_job_arrival j1)
                 (Prosa_Implementation_Definitions_Task_concrete_job_job_arrival j2))
              (instDecidableEqNat (Prosa_Implementation_Definitions_Task_concrete_job_job_arrival j1)
                 (Prosa_Implementation_Definitions_Task_concrete_job_job_arrival j2))))
        (Decidable_decide
           (@eq Nat (Prosa_Implementation_Definitions_Task_concrete_job_job_cost j1)
              (Prosa_Implementation_Definitions_Task_concrete_job_job_cost j2))
           (instDecidableEqNat (Prosa_Implementation_Definitions_Task_concrete_job_job_cost j1)
              (Prosa_Implementation_Definitions_Task_concrete_job_job_cost j2))))
     (Decidable_decide
        (@eq Prosa_Behavior_Time_instant (Prosa_Implementation_Definitions_Task_concrete_job_job_deadline j1)
           (Prosa_Implementation_Definitions_Task_concrete_job_job_deadline j2))
        (instDecidableEqNat (Prosa_Implementation_Definitions_Task_concrete_job_job_deadline j1)
           (Prosa_Implementation_Definitions_Task_concrete_job_job_deadline j2))))
  (Decidable_decide
     (@eq Prosa_Implementation_Definitions_Task_concrete_task
        (Prosa_Implementation_Definitions_Task_concrete_job_job_task j1)
        (Prosa_Implementation_Definitions_Task_concrete_job_job_task j2))
     (Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
        (Prosa_Implementation_Definitions_Task_concrete_job_job_task j1)
        (Prosa_Implementation_Definitions_Task_concrete_job_job_task j2)))
     : Prosa_Implementation_Definitions_Task_concrete_job ->
       Prosa_Implementation_Definitions_Task_concrete_job -> Bool

Arguments Prosa_Implementation_Definitions_Task_job_eqdef j1 j2
```
