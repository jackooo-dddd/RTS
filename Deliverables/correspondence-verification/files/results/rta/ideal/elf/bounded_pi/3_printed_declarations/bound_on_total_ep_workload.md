# `bound_on_total_ep_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload`
- Certificate: `bound_on_total_ep_workload_correspondence`

## Official Rocq

```coq
bound_on_total_ep_workload :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
PriorityPoint Task ->
seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> duration -> duration -> nat

bound_on_total_ep_workload is not universe polymorphic
Arguments bound_on_total_ep_workload {Task H H2 H3} ts%seq_scope tsk FP A Δ
bound_on_total_ep_workload is transparent
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 324, characters 13-39
@bound_on_total_ep_workload
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       PriorityPoint Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> duration -> duration -> nat
```

Body:

```coq
bound_on_total_ep_workload =
fun (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (H3 : PriorityPoint Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (FP : FP_policy Task) 
  (A Δ : duration) =>
\sum_(tsk_o <- ts | @ep_task Task FP tsk tsk_o && (tsk_o != tsk))
   @task_request_bound_function Task H H2 tsk_o
     (minn `|Order.Def.max 0%R (@ep_task_intf_interval Task H3 tsk tsk_o A)| Δ)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       PriorityPoint Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> duration -> duration -> nat

Arguments bound_on_total_ep_workload {Task H H2 H3} ts%seq_scope tsk FP A Δ
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            Task →
              Prosa.Model.Priority.Definitions.FP_policy Task →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            Task →
              Prosa.Model.Priority.Definitions.FP_policy Task →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] ts tsk FP A Δ =>
  Prosa.Util.Sum.sumFiltered ts
    (fun tsk_o => Prosa.Model.Priority.Definitions.ep_task tsk tsk_o && decide (tsk_o ≠ tsk)) fun tsk_o =>
    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_o
      (min (max 0 (Prosa.Results.Rta.Ideal.Elf.BoundedPi.ep_task_intf_interval tsk tsk_o A)).natAbs Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_13 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (inst_16 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (ts : List Task) (tsk : Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (A _UU0394_ : Prosa_Behavior_Time_duration) =>
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
     inst_10
     inst_13 tsk_o
     (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
        (Int_natAbs
           (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
              (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
                 inst_3
                 inst_16 tsk tsk_o A)))
        _UU0394_))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload Task
  inst_3
  inst_10
  inst_13
  inst_16 ts 
  tsk FP A a____at____internal__hyg0
```
