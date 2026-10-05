# `bound_on_athep_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.workload.elf_athep_bound.bound_on_athep_workload`
- Lean: `Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_athep_workload`
- Certificate: `bound_on_athep_workload_correspondence`

## Official Rocq

```coq
bound_on_athep_workload :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
gel.PriorityPoint Task ->
seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> duration -> nat

bound_on_athep_workload is not universe polymorphic
Arguments bound_on_athep_workload {Task H H0 H1} ts%seq_scope {FP} tsk A delta
bound_on_athep_workload is transparent
Expands to: Constant prosa.analysis.definitions.workload.elf_athep_bound.bound_on_athep_workload
Declared in library prosa.analysis.definitions.workload.elf_athep_bound, line 47, characters 13-36
@bound_on_athep_workload
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       gel.PriorityPoint Task ->
       seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> duration -> nat
```

Body:

```coq
bound_on_athep_workload =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : gel.PriorityPoint Task)
  (ts : seq (Equality.sort Task)) (FP : FP_policy Task) (tsk : Equality.sort Task) 
  (A delta : duration) =>
@bound_on_hp_task_workload Task H H0 ts FP tsk delta +
@bound_on_ep_task_workload Task H H0 H1 ts FP tsk A delta
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       gel.PriorityPoint Task ->
       seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> duration -> nat

Arguments bound_on_athep_workload {Task H H0 H1} ts%seq_scope {FP} tsk A delta
```

## Lean

```lean
@Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_athep_workload : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
              Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_athep_workload.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
              Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] ts
    [Prosa.Model.Priority.Definitions.FP_policy Task] tsk A delta =>
  Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_hp_task_workload ts tsk delta +
    Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_ep_task_workload ts tsk A delta
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_athep_workload
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_athep_workload@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (ts : List Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (tsk : Task) (A delta : Prosa_Behavior_Time_duration) =>
HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
  (Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_hp_task_workload Task
     inst_3
     inst_6
     inst_9 ts FP tsk delta)
  (Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_ep_task_workload Task
     inst_3
     inst_6
     inst_9
     inst_12 ts FP tsk A
     delta)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_athep_workload 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts FP tsk A a____at____internal__hyg0
```
