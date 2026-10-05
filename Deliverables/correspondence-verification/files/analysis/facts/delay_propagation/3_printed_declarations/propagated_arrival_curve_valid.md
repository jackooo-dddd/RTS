# `propagated_arrival_curve_valid`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.delay_propagation.propagated_arrival_curve_valid`
- Lean: `Prosa.Analysis.Facts.DelayPropagation.propagated_arrival_curve_valid`
- Certificate: `propagated_arrival_curve_valid_correspondence`

## Official Rocq

```coq
propagated_arrival_curve_valid :
forall {Task1 Task2 : TaskType} (task1_of : Equality.sort Task2 -> Equality.sort Task1)
  (delay_bound : Equality.sort Task2 -> duration) (ts2 : seq (Equality.sort Task2))
  {max_arrivals1 : MaxArrivals Task1},
(forall tsk2 : Equality.sort Task2,
 is_true (tsk2 \in ts2) -> @monotone nat leq (@max_arrivals Task1 max_arrivals1 (task1_of tsk2))) ->
@valid_taskset_arrival_curve Task2 ts2 (@max_arrivals2 Task1 Task2 task1_of delay_bound max_arrivals1)

propagated_arrival_curve_valid is not universe polymorphic
Arguments propagated_arrival_curve_valid {Task1 Task2} (task1_of delay_bound)%function_scope 
  ts2%seq_scope {max_arrivals1} _%function_scope tsk _
propagated_arrival_curve_valid is opaque
Expands to: Constant prosa.analysis.facts.delay_propagation.propagated_arrival_curve_valid
Declared in library prosa.analysis.facts.delay_propagation, line 150, characters 8-38
@propagated_arrival_curve_valid
     : forall (Task1 Task2 : TaskType) (task1_of : Equality.sort Task2 -> Equality.sort Task1)
         (delay_bound : Equality.sort Task2 -> duration) (ts2 : seq (Equality.sort Task2))
         (max_arrivals1 : MaxArrivals Task1),
       (forall tsk2 : Equality.sort Task2,
        is_true (tsk2 \in ts2) -> @monotone nat leq (@max_arrivals Task1 max_arrivals1 (task1_of tsk2))) ->
       @valid_taskset_arrival_curve Task2 ts2 (@max_arrivals2 Task1 Task2 task1_of delay_bound max_arrivals1)
```

## Lean

```lean
@Prosa.Analysis.Facts.DelayPropagation.propagated_arrival_curve_valid : ∀ {Task1 : Prosa.Model.Task.Concept.TaskType}
  {Task2 : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task1] [inst_1 : DecidableEq Task2]
  (task1_of : Task2 → Task1) (delay_bound : Task2 → Prosa.Behavior.Time.duration) (ts2 : List Task2)
  [max_arrivals1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task1],
  (∀ (tsk2 : Task2),
      decide (tsk2 ∈ ts2) = true →
        Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))
          (Prosa.Model.Task.Arrival.Curves.max_arrivals (task1_of tsk2))) →
    Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts2 Prosa.Model.Task.Arrival.Curves.max_arrivals
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_DelayPropagation_propagated_arrival_curve_valid
     : forall (Task1 Task2 : Prosa_Model_Task_Concept_TaskType)
         (inst_4 : DecidableEq Task1)
         (inst_7 : DecidableEq Task2)
         (task1_of : Task2 -> Task1) (delay_bound : Task2 -> Prosa_Behavior_Time_duration) 
         (ts2 : List Task2)
         (max_arrivals1 : Prosa_Model_Task_Arrival_Curves_MaxArrivals Task1
                            inst_4),
       (forall tsk2 : Task2,
        @eq Bool
          (Decidable_decide (Membership_mem Task2 (List Task2) (List_instMembership Task2) ts2 tsk2)
             (List_instDecidableMemOfLawfulBEq Task2
                (instBEqOfDecidableEq Task2
                   inst_7)
                (instLawfulBEq Task2
                   inst_7)
                tsk2 ts2))
          Bool_true ->
        Prosa_Util_Rel_monotone_inst1 Prosa_Behavior_Time_duration
          (fun x y : Prosa_Behavior_Time_duration =>
           Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat x y) (Nat_decLe x y))
          (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task1
             inst_4 max_arrivals1
             (task1_of tsk2))) ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task2
         inst_7 ts2
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task2
            inst_7
            (Prosa_Analysis_Facts_DelayPropagation_max_arrivals2 Task1 Task2
               inst_4
               inst_7 task1_of
               delay_bound max_arrivals1))
```
