# `task_rbf_epsilon_gt_0`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.task_rbf_epsilon_gt_0`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.task_rbf_epsilon_gt_0`
- Certificate: `task_rbf_epsilon_gt_0_correspondence`

## Official Rocq

```coq
task_rbf_epsilon_gt_0 :
forall {Task : TaskType} {H : TaskCost Task} (tsk : Equality.sort Task) {H2 : MaxArrivals Task},
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H2 tsk 1) -> is_true (0 < @task_request_bound_function Task H H2 tsk 1)

task_rbf_epsilon_gt_0 is not universe polymorphic
Arguments task_rbf_epsilon_gt_0 {Task H} tsk {H2} H_positive_cost H_arrival_curve_positive
task_rbf_epsilon_gt_0 is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.task_rbf_epsilon_gt_0
Declared in library prosa.analysis.facts.model.rbf, line 342, characters 8-29
@task_rbf_epsilon_gt_0
     : forall (Task : TaskType) (H : TaskCost Task) (tsk : Equality.sort Task) (H2 : MaxArrivals Task),
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H2 tsk 1) ->
       is_true (0 < @task_request_bound_function Task H H2 tsk 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.task_rbf_epsilon_gt_0 : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] (tsk : Task)
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  0 < Prosa.Model.Task.Concept.task_cost tsk →
    0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
      0 < Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_task_rbf_epsilon_gt_0
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (tsk : Task)
         (inst_10 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_6 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_10 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
            inst_3
            inst_6
            inst_10 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
```
