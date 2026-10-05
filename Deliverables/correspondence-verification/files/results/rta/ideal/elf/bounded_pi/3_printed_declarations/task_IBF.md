# `task_IBF`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.task_IBF`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.task_IBF`
- Certificate: `task_IBF_correspondence`

## Official Rocq

```coq
task_IBF :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
PriorityPoint Task ->
seq (Equality.sort Task) ->
Equality.sort Task -> FP_policy Task -> duration -> (duration -> duration) -> duration -> duration -> nat

task_IBF is not universe polymorphic
Arguments task_IBF {Task H H2 H3} ts%seq_scope tsk FP priority_inversion_lp_tasks_bound
  priority_inversion_ep_tasks_bound%function_scope A Δ
task_IBF is transparent
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.task_IBF
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 331, characters 13-21
@task_IBF
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       PriorityPoint Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task ->
       FP_policy Task -> duration -> (duration -> duration) -> duration -> duration -> nat
```

Body:

```coq
task_IBF =
fun (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (H3 : PriorityPoint Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (FP : FP_policy Task)
  (priority_inversion_lp_tasks_bound : duration) (priority_inversion_ep_tasks_bound : duration -> duration)
  (A Δ : duration) =>
priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A +
@bound_on_total_ep_workload Task H H2 H3 ts tsk FP A Δ + @total_hp_rbf Task H H2 ts tsk FP Δ
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       PriorityPoint Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task ->
       FP_policy Task -> duration -> (duration -> duration) -> duration -> duration -> nat

Arguments task_IBF {Task H H2 H3} ts%seq_scope tsk FP priority_inversion_lp_tasks_bound
  priority_inversion_ep_tasks_bound%function_scope A Δ
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.task_IBF : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            Task →
              Prosa.Model.Priority.Definitions.FP_policy Task →
                Prosa.Behavior.Time.duration →
                  (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
                    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Elf.BoundedPi.task_IBF.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            Task →
              Prosa.Model.Priority.Definitions.FP_policy Task →
                Prosa.Behavior.Time.duration →
                  (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
                    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] ts tsk FP
    priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A Δ =>
  Prosa.Results.Rta.Ideal.Elf.BoundedPi.priority_inversion_bound priority_inversion_lp_tasks_bound
        priority_inversion_ep_tasks_bound A +
      Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload ts tsk FP A Δ +
    Prosa.Results.Rta.Ideal.Elf.BoundedPi.total_hp_rbf ts tsk FP Δ
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_task_IBF
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
       Prosa_Behavior_Time_duration ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_task_IBF@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (priority_inversion_lp_tasks_bound : Prosa_Behavior_Time_duration)
  (priority_inversion_ep_tasks_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
  (A _UU0394_ : Prosa_Behavior_Time_duration) =>
HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
     (Prosa_Results_Rta_Ideal_Elf_BoundedPi_priority_inversion_bound priority_inversion_lp_tasks_bound
        priority_inversion_ep_tasks_bound A)
     (Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload Task
        inst_3
        inst_10
        inst_13
        inst_16 ts tsk FP A _UU0394_))
  (Prosa_Results_Rta_Ideal_Elf_BoundedPi_total_hp_rbf Task
     inst_3
     inst_10
     inst_13 ts tsk FP _UU0394_)
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
       Prosa_Behavior_Time_duration ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Results_Rta_Ideal_Elf_BoundedPi_task_IBF Task
  inst_3
  inst_10
  inst_13
  inst_16 ts 
  tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound%_function_scope 
  A a____at____internal__hyg0
```
