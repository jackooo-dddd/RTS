# `task_request_bound_function`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.request_bound_function.task_request_bound_function`
- Lean: `Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function`
- Certificate: `task_request_bound_function_correspondence`

## Official Rocq

```coq
task_request_bound_function :
forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat

task_request_bound_function is not universe polymorphic
Arguments task_request_bound_function {Task H H0} tsk Δ
task_request_bound_function is transparent
Expands to: Constant prosa.analysis.definitions.request_bound_function.task_request_bound_function
Declared in library prosa.analysis.definitions.request_bound_function, line 22, characters 13-40
@task_request_bound_function
     : forall Task : TaskType, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat
```

Body:

```coq
task_request_bound_function =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (tsk : Equality.sort Task) (Δ : duration) =>
@task_cost Task H tsk * @max_arrivals Task H0 tsk Δ
     : forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat

Arguments task_request_bound_function {Task H H0} tsk Δ
```

## Lean

```lean
@Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk Δ =>
  Prosa.Model.Task.Concept.task_cost tsk * Prosa.Model.Task.Arrival.Curves.max_arrivals tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (_UU0394_ : Prosa_Behavior_Time_duration) =>
HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
  (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
  (Prosa_Model_Task_Concept_TaskCost_task_cost Task
     inst_3
     inst_6 tsk)
  (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
     inst_3
     inst_9 tsk _UU0394_)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function 
  Task inst_3
  inst_6
  inst_9 
  tsk a____at____internal__hyg0
```
