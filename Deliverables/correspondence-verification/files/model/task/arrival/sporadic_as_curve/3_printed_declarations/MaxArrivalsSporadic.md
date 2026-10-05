# `MaxArrivalsSporadic`

- Kind (Rocq): Instance
- Rocq: `prosa.model.task.arrival.sporadic_as_curve.MaxArrivalsSporadic`
- Lean: `Prosa.Model.Task.Arrival.SporadicAsCurve.MaxArrivalsSporadic`
- Certificate: `MaxArrivalsSporadic_correspondence`

## Official Rocq

```coq
MaxArrivalsSporadic : forall {Task : TaskType}, SporadicModel Task -> MaxArrivals Task

MaxArrivalsSporadic is not universe polymorphic
Arguments MaxArrivalsSporadic {Task H} _ _
MaxArrivalsSporadic is transparent
Expands to: Constant prosa.model.task.arrival.sporadic_as_curve.MaxArrivalsSporadic
Declared in library prosa.model.task.arrival.sporadic_as_curve, line 16, characters 2-90
@MaxArrivalsSporadic
     : forall Task : TaskType, SporadicModel Task -> MaxArrivals Task
```

Body:

```coq
MaxArrivalsSporadic =
fun Task : TaskType => [eta @max_sporadic_arrivals Task]
     : forall {Task : TaskType}, SporadicModel Task -> MaxArrivals Task

Arguments MaxArrivalsSporadic {Task H} _ _
```

## Lean

```lean
@Prosa.Model.Task.Arrival.SporadicAsCurve.MaxArrivalsSporadic : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] → Prosa.Model.Task.Arrival.Curves.MaxArrivals Task
```

Body:

```lean
@[instance_reducible] def Prosa.Model.Task.Arrival.SporadicAsCurve.MaxArrivalsSporadic.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] → Prosa.Model.Task.Arrival.Curves.MaxArrivals Task :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] =>
  { max_arrivals := Prosa.Analysis.Facts.Sporadic.ArrivalBound.max_sporadic_arrivals }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_SporadicAsCurve_MaxArrivalsSporadic
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3
```

Body:

```coq
Prosa_Model_Task_Arrival_SporadicAsCurve_MaxArrivalsSporadic@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
     inst_3) =>
Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk Task
  inst_3
  (Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals Task
     inst_3
     inst_6)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3

Arguments Prosa_Model_Task_Arrival_SporadicAsCurve_MaxArrivalsSporadic Task
  inst_3
  inst_6
```
