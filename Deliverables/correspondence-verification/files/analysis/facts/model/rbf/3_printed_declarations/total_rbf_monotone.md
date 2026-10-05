# `total_rbf_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.total_rbf_monotone`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.total_rbf_monotone`
- Certificate: `total_rbf_monotone_correspondence`

## Official Rocq

```coq
total_rbf_monotone :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
@monotone nat leq (@total_request_bound_function Task H H0 ts)

total_rbf_monotone is not universe polymorphic
Arguments total_rbf_monotone {Task H H0} ts%seq_scope H_valid_arrival_curve x y _
total_rbf_monotone is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.total_rbf_monotone
Declared in library prosa.analysis.facts.model.rbf, line 382, characters 8-26
@total_rbf_monotone
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       @monotone nat leq (@total_request_bound_function Task H H0 ts)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.total_rbf_monotone : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))
      (Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_total_rbf_monotone
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_9) ->
       Prosa_Util_Rel_monotone_inst1 Prosa_Behavior_Time_duration
         (fun x y : Prosa_Behavior_Time_duration =>
          Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat x y) (Nat_decLe x y))
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_6
            inst_9 ts)
```
