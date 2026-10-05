# `jobs_remaining`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.maximal_arrival_sequence.jobs_remaining`
- Lean: `Prosa.Implementation.Definitions.MaximalArrivalSequence.jobs_remaining`
- Certificate: `jobs_remaining_correspondence`

## Official Rocq

```coq
jobs_remaining :
forall {Task : TaskType},
MaxArrivals Task ->
Equality.sort Task -> seq nat -> option (Equality.sort Datatypes_nat__canonical__eqtype_Equality)

jobs_remaining is not universe polymorphic
Arguments jobs_remaining {Task H3} tsk arr_prefix%seq_scope
jobs_remaining is transparent
Expands to: Constant prosa.implementation.definitions.maximal_arrival_sequence.jobs_remaining
Declared in library prosa.implementation.definitions.maximal_arrival_sequence, line 49, characters 15-29
@jobs_remaining
     : forall Task : TaskType,
       MaxArrivals Task ->
       Equality.sort Task -> seq nat -> option (Equality.sort Datatypes_nat__canonical__eqtype_Equality)
```

Body:

```coq
jobs_remaining =
fun (Task : TaskType) (H3 : MaxArrivals Task) (tsk : Equality.sort Task) (arr_prefix : seq nat) =>
@supremum Datatypes_nat__canonical__eqtype_Equality leq
  [seq @max_arrivals Task H3 tsk Δ.+1 - suffix_sum arr_prefix Δ | Δ <- iota 0 (@size nat arr_prefix).+1]
     : forall {Task : TaskType},
       MaxArrivals Task ->
       Equality.sort Task -> seq nat -> option (Equality.sort Datatypes_nat__canonical__eqtype_Equality)

Arguments jobs_remaining {Task H3} tsk arr_prefix%seq_scope
```

## Lean

```lean
@Prosa.Implementation.Definitions.MaximalArrivalSequence.jobs_remaining : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → List ℕ → Option ℕ
def Prosa.Implementation.Definitions.MaximalArrivalSequence.jobs_remaining.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → List ℕ → Option ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk arr_prefix =>
  Prosa.Util.Supremum.supremum (fun a b => decide (a ≤ b))
    (List.map
      (fun Δ =>
        Prosa.Model.Task.Arrival.Curves.max_arrivals tsk (Δ + 1) -
          Prosa.Implementation.Definitions.MaximalArrivalSequence.suffix_sum arr_prefix Δ)
      (List.range' 0 (arr_prefix.length + 1)))
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_jobs_remaining
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> List_inst1 Nat -> Option_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_jobs_remaining@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (arr_prefix : List_inst1 Nat) =>
Prosa_Util_Supremum_supremum_inst1 Nat
  (fun a b : Nat => Decidable_decide (LE_le_inst1 Nat instLENat a b) (Nat_decLe a b))
  (List_map_inst3 Prosa_Behavior_Time_duration Nat
     (fun _UU0394_ : Prosa_Behavior_Time_duration =>
      HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
        (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
           inst_3
           inst_6 tsk
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) _UU0394_
              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
        (Prosa_Implementation_Definitions_MaximalArrivalSequence_suffix_sum arr_prefix _UU0394_))
     (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (List_length_inst1 Nat arr_prefix)
           (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> List_inst1 Nat -> Option_inst1 Nat

Arguments Prosa_Implementation_Definitions_MaximalArrivalSequence_jobs_remaining 
  Task inst_3
  inst_6 
  tsk arr_prefix
```
