# `task_rbf_0_zero`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.task_rbf_0_zero`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.task_rbf_0_zero`
- Certificate: `task_rbf_0_zero_correspondence`

## Official Rocq

```coq
task_rbf_0_zero :
forall {Task : TaskType} {H : TaskCost Task} (tsk : Equality.sort Task) {H2 : MaxArrivals Task},
valid_arrival_curve (@max_arrivals Task H2 tsk) -> @task_request_bound_function Task H H2 tsk 0 = 0

task_rbf_0_zero is not universe polymorphic
Arguments task_rbf_0_zero {Task H} tsk {H2} H_valid_arrival_curve
task_rbf_0_zero is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.task_rbf_0_zero
Declared in library prosa.analysis.facts.model.rbf, line 294, characters 8-23
@task_rbf_0_zero
     : forall (Task : TaskType) (H : TaskCost Task) (tsk : Equality.sort Task) (H2 : MaxArrivals Task),
       valid_arrival_curve (@max_arrivals Task H2 tsk) -> @task_request_bound_function Task H H2 tsk 0 = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.task_rbf_0_zero : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] (tsk : Task)
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  Prosa.Model.Task.Arrival.Curves.valid_arrival_curve (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk) →
    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk 0 = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_task_rbf_0_zero
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
       @eq Nat
         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
            inst_3
            inst_6
            inst_10 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
