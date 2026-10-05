# `total_request_bound_function`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.request_bound_function.total_request_bound_function`
- Lean: `Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function`
- Certificate: `total_request_bound_function_correspondence`

## Official Rocq

```coq
total_request_bound_function :
forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> nat

total_request_bound_function is not universe polymorphic
Arguments total_request_bound_function {Task H H0} ts%seq_scope Δ
total_request_bound_function is transparent
Expands to: Constant prosa.analysis.definitions.request_bound_function.total_request_bound_function
Declared in library prosa.analysis.definitions.request_bound_function, line 33, characters 13-41
@total_request_bound_function
     : forall Task : TaskType,
       TaskCost Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> nat
```

Body:

```coq
total_request_bound_function =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (Δ : duration) =>
\sum_(tsk <- ts) @task_request_bound_function Task H H0 tsk Δ
     : forall {Task : TaskType},
       TaskCost Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> nat

Arguments total_request_bound_function {Task H H0} ts%seq_scope Δ
```

## Lean

```lean
@Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → List Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → List Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts Δ =>
  Prosa.Util.Sum.sumSeq ts fun tsk => Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (_UU0394_ : Prosa_Behavior_Time_duration) =>
Prosa_Util_Sum_sumSeq Task ts
  (fun tsk : Task =>
   Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
     inst_3
     inst_6
     inst_9 tsk _UU0394_)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function 
  Task inst_3
  inst_6
  inst_9 
  ts a____at____internal__hyg0
```
