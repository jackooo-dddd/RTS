# `max_arrivals_at`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.maximal_arrival_sequence.max_arrivals_at`
- Lean: `Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at`
- Certificate: `max_arrivals_at_correspondence`

## Official Rocq

```coq
max_arrivals_at : forall {Task : TaskType}, MaxArrivals Task -> Equality.sort Task -> nat -> nat

max_arrivals_at is not universe polymorphic
Arguments max_arrivals_at {Task H3} tsk t%nat_scope
max_arrivals_at is transparent
Expands to: Constant prosa.implementation.definitions.maximal_arrival_sequence.max_arrivals_at
Declared in library prosa.implementation.definitions.maximal_arrival_sequence, line 75, characters 15-30
@max_arrivals_at
     : forall Task : TaskType, MaxArrivals Task -> Equality.sort Task -> nat -> nat
```

Body:

```coq
max_arrivals_at =
fun (Task : TaskType) (H3 : MaxArrivals Task) (tsk : Equality.sort Task) (t : nat) =>
@nth nat 0 (@maximal_arrival_prefix Task H3 tsk t) t
     : forall {Task : TaskType}, MaxArrivals Task -> Equality.sort Task -> nat -> nat

Arguments max_arrivals_at {Task H3} tsk t%nat_scope
```

## Lean

```lean
@Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → ℕ → ℕ
def Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → ℕ → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk t =>
  (Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix tsk t).getD t 0
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Nat -> Nat
```

Body:

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (t : Nat) =>
List_getD_inst1 Nat
  (Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix Task
     inst_3
     inst_6 tsk t)
  t (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Nat -> Nat

Arguments Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at 
  Task inst_3
  inst_6 
  tsk n%_Nat_scope
```
