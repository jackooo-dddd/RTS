# `bound_on_athep_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.workload.edf_athep_bound.bound_on_athep_workload`
- Lean: `Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload`
- Certificate: `bound_on_athep_workload_correspondence`

## Official Rocq

```coq
bound_on_athep_workload :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task -> MaxArrivals Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat -> nat -> nat

bound_on_athep_workload is not universe polymorphic
Arguments bound_on_athep_workload {Task H H0 H1} ts%seq_scope tsk (A Δ)%nat_scope
bound_on_athep_workload is transparent
Expands to: Constant prosa.analysis.definitions.workload.edf_athep_bound.bound_on_athep_workload
Declared in library prosa.analysis.definitions.workload.edf_athep_bound, line 33, characters 13-36
@bound_on_athep_workload
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat -> nat -> nat
```

Body:

```coq
bound_on_athep_workload =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) =>
let D := [eta @task_deadline Task H0] in
let rbf := @task_request_bound_function Task H H1 in
fun A Δ : nat => \sum_(tsk_o <- ts | tsk_o != tsk) rbf tsk_o (minn (A + 1 + D tsk - D tsk_o) Δ)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat -> nat -> nat

Arguments bound_on_athep_workload {Task H H0 H1} ts%seq_scope tsk (A Δ)%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → List Task → Task → ℕ → ℕ → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → List Task → Task → ℕ → ℕ → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts tsk A Δ =>
  Prosa.Util.Sum.sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_o
      (min (A + 1 + Prosa.Model.Task.Concept.task_deadline tsk - Prosa.Model.Task.Concept.task_deadline tsk_o) Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Task -> Nat -> Nat -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Concept_TaskDeadline Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (tsk : Task) (A _UU0394_ : Nat) =>
Prosa_Util_Sum_sumFiltered Task ts
  (fun tsk_o : Task =>
   Decidable_decide (Ne Task tsk_o tsk)
     (instDecidableNot (@eq Task tsk_o tsk)
        (inst_3 tsk_o tsk)))
  (fun tsk_o : Task =>
   Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
     inst_3
     inst_6
     inst_12 tsk_o
     (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
        (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
           (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
              (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                 inst_3
                 inst_9 tsk))
           (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
              inst_3
              inst_9 tsk_o))
        _UU0394_))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Task -> Nat -> Nat -> Nat

Arguments Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts tsk (x n)%_Nat_scope
```
