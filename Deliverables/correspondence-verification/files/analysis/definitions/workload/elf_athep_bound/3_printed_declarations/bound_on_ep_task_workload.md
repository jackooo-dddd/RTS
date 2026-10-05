# `bound_on_ep_task_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.workload.elf_athep_bound.bound_on_ep_task_workload`
- Lean: `Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_ep_task_workload`
- Certificate: `bound_on_ep_task_workload_correspondence`

## Official Rocq

```coq
bound_on_ep_task_workload :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
gel.PriorityPoint Task ->
seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> duration -> nat

bound_on_ep_task_workload is not universe polymorphic
Arguments bound_on_ep_task_workload {Task H H0 H1} ts%seq_scope {FP} tsk A delta
bound_on_ep_task_workload is transparent
Expands to: Constant prosa.analysis.definitions.workload.elf_athep_bound.bound_on_ep_task_workload
Declared in library prosa.analysis.definitions.workload.elf_athep_bound, line 34, characters 13-38
@bound_on_ep_task_workload
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       gel.PriorityPoint Task ->
       seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> duration -> nat
```

Body:

```coq
bound_on_ep_task_workload =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : gel.PriorityPoint Task)
  (ts : seq (Equality.sort Task)) (FP : FP_policy Task) (tsk : Equality.sort Task) 
  (A delta : duration) =>
let rbf_duration :=
  fun tsk_o : Equality.sort Task =>
  minn
    (ssrint.absz
       (@order.Order.max ssrnum.ring_display
          (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
             ssrint.ssrint_int__canonical__Num_POrderedZmodule)
          (@ssralg.GRing.zero
             (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                ssrint.ssrint_int__canonical__Num_POrderedZmodule))
          (@ep_task_interfering_interval_length Task H1 tsk tsk_o A)))
    delta
  in
\sum_(tsk_o <- ts | @ep_task Task FP tsk tsk_o && (tsk_o != tsk))
   @task_request_bound_function Task H H0 tsk_o (rbf_duration tsk_o)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       gel.PriorityPoint Task ->
       seq (Equality.sort Task) -> FP_policy Task -> Equality.sort Task -> duration -> duration -> nat

Arguments bound_on_ep_task_workload {Task H H0 H1} ts%seq_scope {FP} tsk A delta
```

## Lean

```lean
@Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_ep_task_workload : {Task :
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
def Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_ep_task_workload.{u_1} : {Task :
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
  Prosa.Util.Sum.sumFiltered ts
    (fun tsk_o => Prosa.Model.Priority.Definitions.ep_task tsk tsk_o && decide (tsk_o ≠ tsk)) fun tsk_o =>
    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_o
      (min
        (max 0
            (Prosa.Analysis.Definitions.Workload.ElfAthepBound.ep_task_interfering_interval_length tsk tsk_o A)).natAbs
        delta)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_ep_task_workload
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
Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_ep_task_workload@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
Prosa_Util_Sum_sumFiltered Task ts
  (fun tsk_o : Task =>
   Bool_and
     (Prosa_Model_Priority_Definitions_ep_task Task
        inst_3 FP tsk tsk_o)
     (Decidable_decide (Ne Task tsk_o tsk)
        (instDecidableNot (@eq Task tsk_o tsk)
           (inst_3 tsk_o tsk))))
  (fun tsk_o : Task =>
   Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
     inst_3
     inst_6
     inst_9 tsk_o
     (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
        (Int_natAbs
           (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
              (Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length Task
                 inst_3
                 inst_12 tsk
                 tsk_o A)))
        delta))
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

Arguments Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_ep_task_workload 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts FP tsk A a____at____internal__hyg0
```
