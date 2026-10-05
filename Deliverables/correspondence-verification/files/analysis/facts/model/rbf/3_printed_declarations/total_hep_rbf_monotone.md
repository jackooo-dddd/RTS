# `total_hep_rbf_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.total_hep_rbf_monotone`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.total_hep_rbf_monotone`
- Certificate: `total_hep_rbf_monotone_correspondence`

## Official Rocq

```coq
total_hep_rbf_monotone :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
forall {H1 : FP_policy Task} (tsk : Equality.sort Task),
@monotone nat leq (@total_hep_request_bound_function_FP Task H H0 ts H1 tsk)

total_hep_rbf_monotone is not universe polymorphic
Arguments total_hep_rbf_monotone {Task H H0} ts%seq_scope H_valid_arrival_curve {H1} tsk x y _
total_hep_rbf_monotone is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.total_hep_rbf_monotone
Declared in library prosa.analysis.facts.model.rbf, line 390, characters 8-30
@total_hep_rbf_monotone
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       forall (H1 : FP_policy Task) (tsk : Equality.sort Task),
       @monotone nat leq (@total_hep_request_bound_function_FP Task H H0 ts H1 tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.total_hep_rbf_monotone : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk : Task),
      Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))
        (Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_total_hep_rbf_monotone
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
       forall
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (tsk : Task),
       Prosa_Util_Rel_monotone_inst1 Prosa_Behavior_Time_duration
         (fun x y : Prosa_Behavior_Time_duration =>
          Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat x y) (Nat_decLe x y))
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
            inst_3
            inst_6
            inst_9 ts FP tsk)
```
