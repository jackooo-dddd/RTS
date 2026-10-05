# `total_hp_rbf`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.total_hp_rbf`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.total_hp_rbf`
- Certificate: `total_hp_rbf_correspondence`

## Official Rocq

```coq
total_hp_rbf :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task -> seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> duration -> nat

total_hp_rbf is not universe polymorphic
Arguments total_hp_rbf {Task H H2} ts%seq_scope tsk FP Δ
total_hp_rbf is transparent
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.total_hp_rbf
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 310, characters 13-25
@total_hp_rbf
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> duration -> nat
```

Body:

```coq
total_hp_rbf =
fun (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task) =>
(@total_hp_request_bound_function_FP Task H H2 ts)^~ tsk
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> duration -> nat

Arguments total_hp_rbf {Task H H2} ts%seq_scope tsk FP Δ
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.total_hp_rbf : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Task → Prosa.Model.Priority.Definitions.FP_policy Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Elf.BoundedPi.total_hp_rbf.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Task → Prosa.Model.Priority.Definitions.FP_policy Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts tsk FP =>
  Prosa.Analysis.Definitions.RequestBoundFunction.total_hp_request_bound_function_FP ts tsk
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_total_hp_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_total_hp_rbf@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_13 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (tsk : Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3) =>
Prosa_Analysis_Definitions_RequestBoundFunction_total_hp_request_bound_function_FP Task
  inst_3
  inst_10
  inst_13 ts FP tsk
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Results_Rta_Ideal_Elf_BoundedPi_total_hp_rbf Task
  inst_3
  inst_10
  inst_13 ts 
  tsk FP a____at____internal__hyg0
```
