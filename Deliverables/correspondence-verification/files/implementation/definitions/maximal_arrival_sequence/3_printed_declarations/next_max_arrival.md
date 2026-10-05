# `next_max_arrival`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.maximal_arrival_sequence.next_max_arrival`
- Lean: `Prosa.Implementation.Definitions.MaximalArrivalSequence.next_max_arrival`
- Certificate: `next_max_arrival_correspondence`

## Official Rocq

```coq
next_max_arrival :
forall {Task : TaskType},
MaxArrivals Task -> Equality.sort Task -> seq nat -> Equality.sort Datatypes_nat__canonical__eqtype_Equality

next_max_arrival is not universe polymorphic
Arguments next_max_arrival {Task H3} tsk arr_prefix%seq_scope
next_max_arrival is transparent
Expands to: Constant prosa.implementation.definitions.maximal_arrival_sequence.next_max_arrival
Declared in library prosa.implementation.definitions.maximal_arrival_sequence, line 56, characters 15-31
@next_max_arrival
     : forall Task : TaskType,
       MaxArrivals Task ->
       Equality.sort Task -> seq nat -> Equality.sort Datatypes_nat__canonical__eqtype_Equality
```

Body:

```coq
next_max_arrival =
fun (Task : TaskType) (H3 : MaxArrivals Task) (tsk : Equality.sort Task) (arr_prefix : seq nat) =>
match @jobs_remaining Task H3 tsk arr_prefix with
| @Some _ n => n
| @None _ => @max_arrivals Task H3 tsk 1
end
     : forall {Task : TaskType},
       MaxArrivals Task ->
       Equality.sort Task -> seq nat -> Equality.sort Datatypes_nat__canonical__eqtype_Equality

Arguments next_max_arrival {Task H3} tsk arr_prefix%seq_scope
```

## Lean

```lean
@Prosa.Implementation.Definitions.MaximalArrivalSequence.next_max_arrival : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → List ℕ → ℕ
def Prosa.Implementation.Definitions.MaximalArrivalSequence.next_max_arrival.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → List ℕ → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk arr_prefix =>
  match Prosa.Implementation.Definitions.MaximalArrivalSequence.jobs_remaining tsk arr_prefix with
  | none => Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1
  | some n => n
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> List_inst1 Nat -> Nat
```

Body:

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (arr_prefix : List_inst1 Nat) =>
Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival_match_1
  (fun _ : Option_inst1 Nat => Nat)
  (Prosa_Implementation_Definitions_MaximalArrivalSequence_jobs_remaining Task
     inst_3
     inst_6 tsk
     arr_prefix)
  (fun _ : Unit =>
   Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
     inst_3
     inst_6 tsk
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
  (fun a : Nat => a)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> List_inst1 Nat -> Nat

Arguments Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival 
  Task inst_3
  inst_6 
  tsk arr_prefix
```
