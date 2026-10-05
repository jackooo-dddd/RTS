# `sporadic_arrival_curve_valid`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_valid`
- Lean: `Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_arrival_curve_valid`
- Certificate: `sporadic_arrival_curve_valid_correspondence`

## Official Rocq

```coq
sporadic_arrival_curve_valid :
forall {Task : TaskType} {H : SporadicModel Task} (tsk : Equality.sort Task),
valid_arrival_curve (@max_sporadic_arrivals Task H tsk)

sporadic_arrival_curve_valid is not universe polymorphic
Arguments sporadic_arrival_curve_valid {Task H} tsk
sporadic_arrival_curve_valid is opaque
Expands to: Constant prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_valid
Declared in library prosa.model.task.arrival.sporadic_as_curve, line 21, characters 8-36
@sporadic_arrival_curve_valid
     : forall (Task : TaskType) (H : SporadicModel Task) (tsk : Equality.sort Task),
       valid_arrival_curve (@max_sporadic_arrivals Task H tsk)
```

## Lean

```lean
@Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_arrival_curve_valid : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] (tsk : Task),
  Prosa.Model.Task.Arrival.Curves.valid_arrival_curve
    (Prosa.Analysis.Facts.Sporadic.ArrivalBound.max_sporadic_arrivals tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_SporadicAsCurve_sporadic_arrival_curve_valid
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
            inst_3)
         (tsk : Task),
       Prosa_Model_Task_Arrival_Curves_valid_arrival_curve
         (Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals Task
            inst_3
            inst_6 tsk)
```
