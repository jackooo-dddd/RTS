# `sporadic_task_sets_arrival_curve_valid`

- Kind (Rocq): Remark
- Rocq: `prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_arrival_curve_valid`
- Lean: `Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_task_sets_arrival_curve_valid`
- Certificate: `sporadic_task_sets_arrival_curve_valid_correspondence`

## Official Rocq

```coq
sporadic_task_sets_arrival_curve_valid :
forall {Task : TaskType} {H : SporadicModel Task} (ts : TaskSet (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task (@MaxArrivalsSporadic Task H))

sporadic_task_sets_arrival_curve_valid is not universe polymorphic
Arguments sporadic_task_sets_arrival_curve_valid {Task H} ts tsk _
sporadic_task_sets_arrival_curve_valid is opaque
Expands to: Constant prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_arrival_curve_valid
Declared in library prosa.model.task.arrival.sporadic_as_curve, line 32, characters 9-47
@sporadic_task_sets_arrival_curve_valid
     : forall (Task : TaskType) (H : SporadicModel Task) (ts : TaskSet (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task (@MaxArrivalsSporadic Task H))
```

## Lean

```lean
@Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_task_sets_arrival_curve_valid : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_SporadicAsCurve_sporadic_task_sets_arrival_curve_valid
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
            inst_3)
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            (Prosa_Model_Task_Arrival_SporadicAsCurve_MaxArrivalsSporadic Task
               inst_3
               inst_6))
```
