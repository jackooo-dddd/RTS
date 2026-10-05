# `blocking_relevant`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.blocking_bound.edf.blocking_relevant`
- Lean: `Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_relevant`
- Certificate: `blocking_relevant_correspondence`

## Official Rocq

```coq
blocking_relevant : forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> bool

blocking_relevant is not universe polymorphic
Arguments blocking_relevant {Task H H2} tsk_o
blocking_relevant is transparent
Expands to: Constant prosa.analysis.definitions.blocking_bound.edf.blocking_relevant
Declared in library prosa.analysis.definitions.blocking_bound.edf, line 28, characters 13-30
@blocking_relevant
     : forall Task : TaskType, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> bool
```

Body:

```coq
blocking_relevant =
fun (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (tsk_o : Equality.sort Task) =>
(0 < @max_arrivals Task H2 tsk_o 1) && (0 < @task_cost Task H tsk_o)
     : forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> bool

Arguments blocking_relevant {Task H H2} tsk_o
```

## Lean

```lean
@Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_relevant : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_relevant.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk_o =>
  decide (0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk_o 1) &&
    decide (0 < Prosa.Model.Task.Concept.task_cost tsk_o)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk_o : Task) =>
Bool_and
  (Decidable_decide
     (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
        (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
           inst_3
           inst_9 tsk_o
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
     (Nat_decLt (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
        (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
           inst_3
           inst_9 tsk_o
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
  (Decidable_decide
     (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
        (Prosa_Model_Task_Concept_TaskCost_task_cost Task
           inst_3
           inst_6 tsk_o))
     (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
        (Prosa_Model_Task_Concept_TaskCost_task_cost Task
           inst_3
           inst_6 tsk_o)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Bool

Arguments Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant Task
  inst_3
  inst_6
  inst_9 
  tsk_o
```
