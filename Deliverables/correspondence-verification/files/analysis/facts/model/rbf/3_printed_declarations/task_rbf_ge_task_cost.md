# `task_rbf_ge_task_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.task_rbf_ge_task_cost`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.task_rbf_ge_task_cost`
- Certificate: `task_rbf_ge_task_cost_correspondence`

## Official Rocq

```coq
task_rbf_ge_task_cost :
forall {Task : TaskType} {H : TaskCost Task} (tsk : Equality.sort Task) {H2 : MaxArrivals Task},
valid_arrival_curve (@max_arrivals Task H2 tsk) ->
is_true (0 < @max_arrivals Task H2 tsk 1) ->
forall A : nat,
is_true (0 < A) -> is_true (@task_cost Task H tsk <= @task_request_bound_function Task H H2 tsk A)

task_rbf_ge_task_cost is not universe polymorphic
Arguments task_rbf_ge_task_cost {Task H} tsk {H2} H_valid_arrival_curve H_arrival_curve_positive 
  A%nat_scope _
task_rbf_ge_task_cost is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.task_rbf_ge_task_cost
Declared in library prosa.analysis.facts.model.rbf, line 331, characters 8-29
@task_rbf_ge_task_cost
     : forall (Task : TaskType) (H : TaskCost Task) (tsk : Equality.sort Task) (H2 : MaxArrivals Task),
       valid_arrival_curve (@max_arrivals Task H2 tsk) ->
       is_true (0 < @max_arrivals Task H2 tsk 1) ->
       forall A : nat,
       is_true (0 < A) -> is_true (@task_cost Task H tsk <= @task_request_bound_function Task H H2 tsk A)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.task_rbf_ge_task_cost : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] (tsk : Task)
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  Prosa.Model.Task.Arrival.Curves.valid_arrival_curve (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk) →
    0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
      ∀ (A : ℕ),
        0 < A →
          Prosa.Model.Task.Concept.task_cost tsk ≤
            Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk A
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_task_rbf_ge_task_cost
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (tsk : Task)
         (inst_10 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3),
       Prosa_Model_Task_Arrival_Curves_valid_arrival_curve
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_10 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_10 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) A ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_6 tsk)
         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
            inst_3
            inst_6
            inst_10 tsk A)
```
