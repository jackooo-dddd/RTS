# `total_demand_bound_function`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.demand_bound_function.total_demand_bound_function`
- Lean: `Prosa.Analysis.Definitions.DemandBoundFunction.total_demand_bound_function`
- Certificate: `total_demand_bound_function_correspondence`

## Official Rocq

```coq
total_demand_bound_function :
forall {Task : TaskType},
TaskCost Task -> TaskDeadline Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> nat

total_demand_bound_function is not universe polymorphic
Arguments total_demand_bound_function {Task H H0 H1} ts%seq_scope delta
total_demand_bound_function is transparent
Expands to: Constant prosa.analysis.definitions.demand_bound_function.total_demand_bound_function
Declared in library prosa.analysis.definitions.demand_bound_function, line 19, characters 13-40
@total_demand_bound_function
     : forall Task : TaskType,
       TaskCost Task -> TaskDeadline Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> nat
```

Body:

```coq
total_demand_bound_function =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
  (ts : seq (Equality.sort Task)) (delta : duration) =>
\sum_(tsk <- ts) @task_demand_bound_function Task H H0 H1 tsk delta
     : forall {Task : TaskType},
       TaskCost Task -> TaskDeadline Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> nat

Arguments total_demand_bound_function {Task H H0 H1} ts%seq_scope delta
```

## Lean

```lean
@Prosa.Analysis.Definitions.DemandBoundFunction.total_demand_bound_function : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → List Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.DemandBoundFunction.total_demand_bound_function.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → List Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts delta =>
  Prosa.Util.Sum.sumSeq ts fun tsk =>
    Prosa.Analysis.Definitions.DemandBoundFunction.task_demand_bound_function tsk delta
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DemandBoundFunction_total_demand_bound_function
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_DemandBoundFunction_total_demand_bound_function@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (ts : List Task) (delta : Prosa_Behavior_Time_duration) =>
Prosa_Util_Sum_sumSeq Task ts
  (fun tsk : Task =>
   Prosa_Analysis_Definitions_DemandBoundFunction_task_demand_bound_function Task
     inst_3
     inst_6
     inst_9
     inst_12 tsk delta)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Definitions_DemandBoundFunction_total_demand_bound_function 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts a____at____internal__hyg0
```
