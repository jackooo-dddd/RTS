# `task_cost_le_sum_rbf`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.task_cost_le_sum_rbf`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.task_cost_le_sum_rbf`
- Certificate: `task_cost_le_sum_rbf_correspondence`

## Official Rocq

```coq
task_cost_le_sum_rbf :
forall {Task : TaskType} {H : TaskCost Task} (tsk : Equality.sort Task) {H2 : MaxArrivals Task},
valid_arrival_curve (@max_arrivals Task H2 tsk) ->
is_true (0 < @max_arrivals Task H2 tsk 1) ->
forall ts : seq (Equality.sort Task),
is_true (tsk \in ts) ->
forall t : nat,
is_true (0 < t) -> is_true (@task_cost Task H tsk <= @total_request_bound_function Task H H2 ts t)

task_cost_le_sum_rbf is not universe polymorphic
Arguments task_cost_le_sum_rbf {Task H} tsk {H2} H_valid_arrival_curve H_arrival_curve_positive 
  ts%seq_scope H_tsk_in_ts t%nat_scope _
task_cost_le_sum_rbf is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.task_cost_le_sum_rbf
Declared in library prosa.analysis.facts.model.rbf, line 354, characters 8-28
@task_cost_le_sum_rbf
     : forall (Task : TaskType) (H : TaskCost Task) (tsk : Equality.sort Task) (H2 : MaxArrivals Task),
       valid_arrival_curve (@max_arrivals Task H2 tsk) ->
       is_true (0 < @max_arrivals Task H2 tsk 1) ->
       forall ts : seq (Equality.sort Task),
       is_true (tsk \in ts) ->
       forall t : nat,
       is_true (0 < t) -> is_true (@task_cost Task H tsk <= @total_request_bound_function Task H H2 ts t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.task_cost_le_sum_rbf : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] (tsk : Task)
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  Prosa.Model.Task.Arrival.Curves.valid_arrival_curve (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk) →
    0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
      ∀ (ts : List Task),
        decide (tsk ∈ ts) = true →
          ∀ (t : ℕ),
            0 < t →
              Prosa.Model.Task.Concept.task_cost tsk ≤
                Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_task_cost_le_sum_rbf
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
       forall ts : List Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task inst_3)
               (instLawfulBEq Task inst_3) tsk
               ts))
         Bool_true ->
       forall t : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) t ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_6 tsk)
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_6
            inst_10 ts t)
```
