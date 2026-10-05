# `valid_periods_imply_pos_hp`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.hyperperiod.valid_periods_imply_pos_hp`
- Lean: `Prosa.Analysis.Facts.Hyperperiod.valid_periods_imply_pos_hp`
- Certificate: `valid_periods_imply_pos_hp_correspondence`

## Official Rocq

```coq
valid_periods_imply_pos_hp :
forall {Task : TaskType} {H : PeriodicModel Task} (ts : TaskSet (Equality.sort Task)),
@valid_periods Task H ts -> is_true (0 < @hyperperiod Task H ts)

valid_periods_imply_pos_hp is not universe polymorphic
Arguments valid_periods_imply_pos_hp {Task H} ts H_valid_periods
valid_periods_imply_pos_hp is opaque
Expands to: Constant prosa.analysis.facts.hyperperiod.valid_periods_imply_pos_hp
Declared in library prosa.analysis.facts.hyperperiod, line 43, characters 8-34
@valid_periods_imply_pos_hp
     : forall (Task : TaskType) (H : PeriodicModel Task) (ts : TaskSet (Equality.sort Task)),
       @valid_periods Task H ts -> is_true (0 < @hyperperiod Task H ts)
```

## Lean

```lean
@Prosa.Analysis.Facts.Hyperperiod.valid_periods_imply_pos_hp : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task]
  (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Arrival.Periodic.valid_periods ts → 0 < Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Hyperperiod_valid_periods_imply_pos_hp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
       Prosa_Model_Task_Arrival_Periodic_valid_periods Task
         inst_3
         inst_6 ts ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
            inst_3
            inst_6 ts)
```
