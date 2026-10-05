# `max_sporadic_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.sporadic.arrival_bound.max_sporadic_arrivals`
- Lean: `Prosa.Analysis.Facts.Sporadic.ArrivalBound.max_sporadic_arrivals`
- Certificate: `max_sporadic_arrivals_correspondence`

## Official Rocq

```coq
max_sporadic_arrivals : forall {Task : TaskType}, SporadicModel Task -> Equality.sort Task -> duration -> nat

max_sporadic_arrivals is not universe polymorphic
Arguments max_sporadic_arrivals {Task H} tsk delta
max_sporadic_arrivals is transparent
Expands to: Constant prosa.analysis.facts.sporadic.arrival_bound.max_sporadic_arrivals
Declared in library prosa.analysis.facts.sporadic.arrival_bound, line 21, characters 13-34
@max_sporadic_arrivals
     : forall Task : TaskType, SporadicModel Task -> Equality.sort Task -> duration -> nat
```

Body:

```coq
max_sporadic_arrivals =
fun (Task : TaskType) (H : SporadicModel Task) (tsk : Equality.sort Task) =>
div_ceil^~ (@task_min_inter_arrival_time Task H tsk)
     : forall {Task : TaskType}, SporadicModel Task -> Equality.sort Task -> duration -> nat

Arguments max_sporadic_arrivals {Task H} tsk delta
```

## Lean

```lean
@Prosa.Analysis.Facts.Sporadic.ArrivalBound.max_sporadic_arrivals : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] → Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Facts.Sporadic.ArrivalBound.max_sporadic_arrivals.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] tsk delta =>
  Prosa.Util.Div_mod.div_ceil delta (Prosa.Model.Task.Arrival.Sporadic.task_min_inter_arrival_time tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
     inst_3)
  (tsk : Task) (delta : Prosa_Behavior_Time_duration) =>
Prosa_Util_Div_mod_div_ceil delta
  (Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task
     inst_3
     inst_6 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals Task
  inst_3
  inst_6 
  tsk delta
```
