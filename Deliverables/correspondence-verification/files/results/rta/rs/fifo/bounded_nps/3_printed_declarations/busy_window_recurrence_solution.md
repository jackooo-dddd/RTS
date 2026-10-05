# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.rs.fifo.bounded_nps.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Rs.Fifo.BoundedNps.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task -> MaxArrivals Task -> seq (Equality.sort Task) -> SupplyBoundFunction -> duration -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H0} ts%seq_scope {SBF} L
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.rs.fifo.bounded_nps.busy_window_recurrence_solution
Declared in library prosa.results.rta.rs.fifo.bounded_nps, line 159, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> SupplyBoundFunction -> duration -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (SBF : SupplyBoundFunction) (L : duration) =>
is_true (0 < L) /\ is_true (@total_request_bound_function Task H H0 ts L <= SBF L)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> SupplyBoundFunction -> duration -> Prop

Arguments busy_window_recurrence_solution {Task H H0} ts%seq_scope {SBF} L
```

## Lean

```lean
@Prosa.Results.Rta.Rs.Fifo.BoundedNps.busy_window_recurrence_solution : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Results.Rta.Rs.Fifo.BoundedNps.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts SBF L =>
  0 < L ∧
    Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L ≤
      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Rs_Fifo_BoundedNps_busy_window_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Results_Rta_Rs_Fifo_BoundedNps_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
  (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
  (ts : List Task) (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction)
  (L : Prosa_Behavior_Time_duration) =>
And
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L)
  (LE_le_inst1 Nat instLENat
     (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
        inst_3
        inst_6
        inst_9 ts L)
     (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF L))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Results_Rta_Rs_Fifo_BoundedNps_busy_window_recurrence_solution Task
  inst_3
  inst_6
  inst_9 ts SBF 
  L
```
