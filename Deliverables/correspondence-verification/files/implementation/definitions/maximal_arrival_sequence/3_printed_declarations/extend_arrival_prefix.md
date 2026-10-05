# `extend_arrival_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.maximal_arrival_sequence.extend_arrival_prefix`
- Lean: `Prosa.Implementation.Definitions.MaximalArrivalSequence.extend_arrival_prefix`
- Certificate: `extend_arrival_prefix_correspondence`

## Official Rocq

```coq
extend_arrival_prefix :
forall {Task : TaskType}, MaxArrivals Task -> Equality.sort Task -> seq nat -> seq nat

extend_arrival_prefix is not universe polymorphic
Arguments extend_arrival_prefix {Task H3} tsk arr_prefix%seq_scope
extend_arrival_prefix is transparent
Expands to: Constant prosa.implementation.definitions.maximal_arrival_sequence.extend_arrival_prefix
Declared in library prosa.implementation.definitions.maximal_arrival_sequence, line 63, characters 15-36
@extend_arrival_prefix
     : forall Task : TaskType, MaxArrivals Task -> Equality.sort Task -> seq nat -> seq nat
```

Body:

```coq
extend_arrival_prefix =
fun (Task : TaskType) (H3 : MaxArrivals Task) (tsk : Equality.sort Task) (arr_prefix : seq nat) =>
arr_prefix ++ [:: @next_max_arrival Task H3 tsk arr_prefix]
     : forall {Task : TaskType}, MaxArrivals Task -> Equality.sort Task -> seq nat -> seq nat

Arguments extend_arrival_prefix {Task H3} tsk arr_prefix%seq_scope
```

## Lean

```lean
@Prosa.Implementation.Definitions.MaximalArrivalSequence.extend_arrival_prefix : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → List ℕ → List ℕ
def Prosa.Implementation.Definitions.MaximalArrivalSequence.extend_arrival_prefix.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → List ℕ → List ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk arr_prefix =>
  arr_prefix ++ [Prosa.Implementation.Definitions.MaximalArrivalSequence.next_max_arrival tsk arr_prefix]
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> List_inst1 Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (arr_prefix : List_inst1 Nat) =>
HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
  (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat)) arr_prefix
  (List_cons_inst1 Nat
     (Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival Task
        inst_3
        inst_6 tsk
        arr_prefix)
     (List_nil_inst1 Nat))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> List_inst1 Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix 
  Task inst_3
  inst_6 
  tsk arr_prefix
```
