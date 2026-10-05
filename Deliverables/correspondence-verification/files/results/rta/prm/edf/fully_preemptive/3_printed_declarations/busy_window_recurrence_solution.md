# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.prm.edf.fully_preemptive.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Prm.Edf.FullyPreemptive.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> duration -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H1} ts%seq_scope Π γ L
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.prm.edf.fully_preemptive.busy_window_recurrence_solution
Declared in library prosa.results.rta.prm.edf.fully_preemptive, line 129, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> duration -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H1 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (Π γ L : duration) =>
is_true (0 < L) /\ is_true (@total_request_bound_function Task H H1 ts L <= prm_sbf Π γ L)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> duration -> Prop

Arguments busy_window_recurrence_solution {Task H H1} ts%seq_scope Π γ L
```

## Lean

```lean
@Prosa.Results.Rta.Prm.Edf.FullyPreemptive.busy_window_recurrence_solution : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Results.Rta.Prm.Edf.FullyPreemptive.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts Pi γ L =>
  0 < L ∧
    Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L ≤
      Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf Pi γ L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Prm_Edf_FullyPreemptive_busy_window_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Results_Rta_Prm_Edf_FullyPreemptive_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (Pi _UU03b3_ L : Prosa_Behavior_Time_duration) =>
And
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L)
  (LE_le_inst1 Nat instLENat
     (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
        inst_3
        inst_6
        inst_9 ts L)
     (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf Pi _UU03b3_ L))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Results_Rta_Prm_Edf_FullyPreemptive_busy_window_recurrence_solution 
  Task inst_3
  inst_6
  inst_9 
  ts Pi _UU03b3_ L
```
