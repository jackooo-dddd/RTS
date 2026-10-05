# `total_hp_request_bound_function_FP`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.request_bound_function.total_hp_request_bound_function_FP`
- Lean: `Prosa.Analysis.Definitions.RequestBoundFunction.total_hp_request_bound_function_FP`
- Certificate: `total_hp_request_bound_function_FP_correspondence`

## Official Rocq

```coq
total_hp_request_bound_function_FP :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task -> seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> nat

total_hp_request_bound_function_FP is not universe polymorphic
Arguments total_hp_request_bound_function_FP {Task H H0} ts%seq_scope {H1} tsk Δ
total_hp_request_bound_function_FP is transparent
Expands to: Constant prosa.analysis.definitions.request_bound_function.total_hp_request_bound_function_FP
Declared in library prosa.analysis.definitions.request_bound_function, line 62, characters 13-47
@total_hp_request_bound_function_FP
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> nat
```

Body:

```coq
total_hp_request_bound_function_FP =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (H1 : FP_policy Task) (tsk : Equality.sort Task) (Δ : duration) =>
\sum_(tsk_other <- ts | @hp_task Task H1 tsk_other tsk) @task_request_bound_function Task H H0 tsk_other Δ
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> nat

Arguments total_hp_request_bound_function_FP {Task H H0} ts%seq_scope {H1} tsk Δ
```

## Lean

```lean
@Prosa.Analysis.Definitions.RequestBoundFunction.total_hp_request_bound_function_FP : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.RequestBoundFunction.total_hp_request_bound_function_FP.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts [Prosa.Model.Priority.Definitions.FP_policy Task] tsk Δ =>
  Prosa.Util.Sum.sumFiltered ts (fun tsk_other => Prosa.Model.Priority.Definitions.hp_task tsk_other tsk)
    fun tsk_other => Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_other Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_RequestBoundFunction_total_hp_request_bound_function_FP
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_RequestBoundFunction_total_hp_request_bound_function_FP@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (tsk : Task) (_UU0394_ : Prosa_Behavior_Time_duration) =>
Prosa_Util_Sum_sumFiltered Task ts
  (fun tsk_other : Task =>
   Prosa_Model_Priority_Definitions_hp_task Task
     inst_3 FP tsk_other tsk)
  (fun tsk_other : Task =>
   Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
     inst_3
     inst_6
     inst_9 tsk_other _UU0394_)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Definitions_RequestBoundFunction_total_hp_request_bound_function_FP 
  Task inst_3
  inst_6
  inst_9 
  ts FP tsk a____at____internal__hyg0
```
