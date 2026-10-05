# `maximal_arrival_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.maximal_arrival_sequence.maximal_arrival_prefix`
- Lean: `Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix`
- Certificate: `maximal_arrival_prefix_correspondence`

## Official Rocq

```coq
maximal_arrival_prefix : forall {Task : TaskType}, MaxArrivals Task -> Equality.sort Task -> nat -> seq nat

maximal_arrival_prefix is not universe polymorphic
Arguments maximal_arrival_prefix {Task H3} tsk t%nat_scope
maximal_arrival_prefix is transparent
Expands to: Constant prosa.implementation.definitions.maximal_arrival_sequence.maximal_arrival_prefix
Declared in library prosa.implementation.definitions.maximal_arrival_sequence, line 68, characters 15-37
@maximal_arrival_prefix
     : forall Task : TaskType, MaxArrivals Task -> Equality.sort Task -> nat -> seq nat
```

Body:

```coq
maximal_arrival_prefix =
fun (Task : TaskType) (H3 : MaxArrivals Task) (tsk : Equality.sort Task) (t : nat) =>
@iter (seq nat) t.+1 (@extend_arrival_prefix Task H3 tsk) [::]
     : forall {Task : TaskType}, MaxArrivals Task -> Equality.sort Task -> nat -> seq nat

Arguments maximal_arrival_prefix {Task H3} tsk t%nat_scope
```

## Lean

```lean
@Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → ℕ → List ℕ
def Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → ℕ → List ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk t =>
  Nat.repeat (Prosa.Implementation.Definitions.MaximalArrivalSequence.extend_arrival_prefix tsk) (t + 1) []
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (t : Nat) =>
Nat_repeat_inst1 (List_inst1 Nat)
  (Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix Task
     inst_3
     inst_6 tsk)
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
  (List_nil_inst1 Nat)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix 
  Task inst_3
  inst_6 
  tsk x____at___Init_Data_List_Basic527151790__hygCtx__hyg16%_Nat_scope
```
