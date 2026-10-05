# `task_max_rbf`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.curve_as_rbf.task_max_rbf`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.task_max_rbf`
- Certificate: `task_max_rbf_correspondence`

## Official Rocq

```coq
task_max_rbf :
forall {Task : TaskType},
TaskCost Task -> (Equality.sort Task -> duration -> nat) -> Equality.sort Task -> duration -> nat

task_max_rbf is not universe polymorphic
Arguments task_max_rbf {Task H} arrivals%function_scope task Δ
task_max_rbf is transparent
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.task_max_rbf
Declared in library prosa.model.task.arrival.curve_as_rbf, line 27, characters 13-25
@task_max_rbf
     : forall Task : TaskType,
       TaskCost Task -> (Equality.sort Task -> duration -> nat) -> Equality.sort Task -> duration -> nat
```

Body:

```coq
task_max_rbf =
fun (Task : TaskType) (H : TaskCost Task) (arrivals : Equality.sort Task -> duration -> nat)
  (task : Equality.sort Task) (Δ : duration) =>
@task_cost Task H task * arrivals task Δ
     : forall {Task : TaskType},
       TaskCost Task -> (Equality.sort Task -> duration -> nat) -> Equality.sort Task -> duration -> nat

Arguments task_max_rbf {Task H} arrivals%function_scope task Δ
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.task_max_rbf : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      (Task → Prosa.Behavior.Time.duration → ℕ) → Task → Prosa.Behavior.Time.duration → ℕ
def Prosa.Model.Task.Arrival.CurveAsRbf.task_max_rbf.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      (Task → Prosa.Behavior.Time.duration → ℕ) → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] arrivals task Δ =>
  Prosa.Model.Task.Concept.task_cost task * arrivals task Δ
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_task_max_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       (Task -> Prosa_Behavior_Time_duration -> Nat) -> Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_task_max_rbf@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
  (arrivals : Task -> Prosa_Behavior_Time_duration -> Nat) (task : Task)
  (_UU0394_ : Prosa_Behavior_Time_duration) =>
HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
  (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
  (Prosa_Model_Task_Concept_TaskCost_task_cost Task
     inst_3
     inst_6 task)
  (arrivals task _UU0394_)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       (Task -> Prosa_Behavior_Time_duration -> Nat) -> Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Model_Task_Arrival_CurveAsRbf_task_max_rbf Task
  inst_3
  inst_6 arrivals%_function_scope 
  task a____at____internal__hyg0
```
