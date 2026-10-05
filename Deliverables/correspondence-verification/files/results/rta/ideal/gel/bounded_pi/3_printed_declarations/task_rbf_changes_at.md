# `task_rbf_changes_at`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.gel.bounded_pi.task_rbf_changes_at`
- Lean: `Prosa.Results.Rta.Ideal.Gel.BoundedPi.task_rbf_changes_at`
- Certificate: `task_rbf_changes_at_correspondence`

## Official Rocq

```coq
task_rbf_changes_at :
forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> bool

task_rbf_changes_at is not universe polymorphic
Arguments task_rbf_changes_at {Task H H2} tsk A
task_rbf_changes_at is transparent
Expands to: Constant prosa.results.rta.ideal.gel.bounded_pi.task_rbf_changes_at
Declared in library prosa.results.rta.ideal.gel.bounded_pi, line 257, characters 13-32
@task_rbf_changes_at
     : forall Task : TaskType, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> bool
```

Body:

```coq
task_rbf_changes_at =
fun (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (tsk : Equality.sort Task) (A : duration) =>
@task_request_bound_function Task H H2 tsk A != @task_request_bound_function Task H H2 tsk (A + 1)
     : forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> bool

Arguments task_rbf_changes_at {Task H H2} tsk A
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Gel.BoundedPi.task_rbf_changes_at : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Gel.BoundedPi.task_rbf_changes_at.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk A =>
  decide
    (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk A ≠
      Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1))
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_task_rbf_changes_at
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_task_rbf_changes_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_13 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (A : Prosa_Behavior_Time_duration) =>
Decidable_decide
  (Ne Nat
     (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
        inst_3
        inst_10
        inst_13 tsk A)
     (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
        inst_3
        inst_10
        inst_13 tsk
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
           Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
  (instDecidableNot
     (@eq Nat
        (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
           inst_3
           inst_10
           inst_13 tsk A)
        (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
           inst_3
           inst_10
           inst_13 tsk
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
     (instDecidableEqNat
        (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
           inst_3
           inst_10
           inst_13 tsk A)
        (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
           inst_3
           inst_10
           inst_13 tsk
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Results_Rta_Ideal_Gel_BoundedPi_task_rbf_changes_at Task
  inst_3
  inst_10
  inst_13 tsk 
  R
```
