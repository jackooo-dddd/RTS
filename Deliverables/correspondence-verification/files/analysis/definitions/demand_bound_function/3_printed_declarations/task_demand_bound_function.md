# `task_demand_bound_function`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.demand_bound_function.task_demand_bound_function`
- Lean: `Prosa.Analysis.Definitions.DemandBoundFunction.task_demand_bound_function`
- Certificate: `task_demand_bound_function_correspondence`

## Official Rocq

```coq
task_demand_bound_function :
forall {Task : TaskType},
TaskCost Task -> TaskDeadline Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat

task_demand_bound_function is not universe polymorphic
Arguments task_demand_bound_function {Task H H0 H1} tsk delta
task_demand_bound_function is transparent
Expands to: Constant prosa.analysis.definitions.demand_bound_function.task_demand_bound_function
Declared in library prosa.analysis.definitions.demand_bound_function, line 14, characters 13-39
@task_demand_bound_function
     : forall Task : TaskType,
       TaskCost Task -> TaskDeadline Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat
```

Body:

```coq
task_demand_bound_function =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
  (tsk : Equality.sort Task) (delta : duration) =>
let delta' := delta - (@task_deadline Task H0 tsk - 1) in @task_request_bound_function Task H H1 tsk delta'
     : forall {Task : TaskType},
       TaskCost Task -> TaskDeadline Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat

Arguments task_demand_bound_function {Task H H0 H1} tsk delta
```

## Lean

```lean
@Prosa.Analysis.Definitions.DemandBoundFunction.task_demand_bound_function : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.DemandBoundFunction.task_demand_bound_function.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk delta =>
  have delta' := delta - (Prosa.Model.Task.Concept.task_deadline tsk - 1);
  Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk delta'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DemandBoundFunction_task_demand_bound_function
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_DemandBoundFunction_task_demand_bound_function@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (tsk : Task) (delta : Prosa_Behavior_Time_duration) =>
let delta' :=
  HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) delta
    (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
       (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
       (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
          inst_3
          inst_9 tsk)
       (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
  in
Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
  inst_3
  inst_6
  inst_12 tsk delta'
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Definitions_DemandBoundFunction_task_demand_bound_function 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  tsk a____at____internal__hyg0
```
