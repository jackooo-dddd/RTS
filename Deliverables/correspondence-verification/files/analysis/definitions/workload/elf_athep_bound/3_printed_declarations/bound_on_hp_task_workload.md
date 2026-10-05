# `bound_on_hp_task_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.workload.elf_athep_bound.bound_on_hp_task_workload`
- Lean: `Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_hp_task_workload`
- Certificate: `bound_on_hp_task_workload_correspondence`

## Official Rocq

```coq
bound_on_hp_task_workload :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task -> seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> nat

bound_on_hp_task_workload is not universe polymorphic
Arguments bound_on_hp_task_workload {Task H H0} ts%seq_scope {FP} tsk delta
bound_on_hp_task_workload is transparent
Expands to: Constant prosa.analysis.definitions.workload.elf_athep_bound.bound_on_hp_task_workload
Declared in library prosa.analysis.definitions.workload.elf_athep_bound, line 41, characters 13-38
@bound_on_hp_task_workload
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> nat
```

Body:

```coq
bound_on_hp_task_workload =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (FP : FP_policy Task) (tsk : Equality.sort Task) =>
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> nat

Arguments bound_on_hp_task_workload {Task H H0} ts%seq_scope {FP} tsk delta
```

## Lean

```lean
@Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_hp_task_workload : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_hp_task_workload.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts [Prosa.Model.Priority.Definitions.FP_policy Task] tsk delta =>
  Prosa.Analysis.Definitions.RequestBoundFunction.total_hp_request_bound_function_FP ts tsk delta
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_hp_task_workload
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
Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_hp_task_workload@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (tsk : Task) (delta : Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_RequestBoundFunction_total_hp_request_bound_function_FP Task
  inst_3
  inst_6
  inst_9 ts FP tsk delta
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

Arguments Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_hp_task_workload 
  Task inst_3
  inst_6
  inst_9 
  ts FP tsk a____at____internal__hyg0
```
