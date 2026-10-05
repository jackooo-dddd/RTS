# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.prm.edf.fully_nonpreemptive.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Prm.Edf.FullyNonpreemptive.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
MaxArrivals Task ->
seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H0 H1} ts%seq_scope tsk Π γ L
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.prm.edf.fully_nonpreemptive.busy_window_recurrence_solution
Declared in library prosa.results.rta.prm.edf.fully_nonpreemptive, line 131, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (Π γ L : duration) =>
is_true (0 < L) /\
is_true (@total_request_bound_function Task H H1 ts L <= prm_sbf Π γ L) /\
is_true
  (@longest_busy_interval_with_pi Task H H0 (@fully_nonpreemptive_task_model Task H) H1 ts tsk <=
   prm_sbf Π γ L)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> Prop

Arguments busy_window_recurrence_solution {Task H H0 H1} ts%seq_scope tsk Π γ L
```

## Lean

```lean
@Prosa.Results.Rta.Prm.Edf.FullyNonpreemptive.busy_window_recurrence_solution : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          List Task →
            Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Results.Rta.Prm.Edf.FullyNonpreemptive.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          List Task →
            Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts tsk Pi γ L =>
  0 < L ∧
    Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L ≤
        Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf Pi γ L ∧
      Prosa.Analysis.Definitions.BusyInterval.EdfPiBound.longest_busy_interval_with_pi ts tsk ≤
        Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf Pi γ L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Prm_Edf_FullyNonpreemptive_busy_window_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Results_Rta_Prm_Edf_FullyNonpreemptive_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Concept_TaskDeadline Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (tsk : Task) (Pi _UU03b3_ L : Prosa_Behavior_Time_duration) =>
And
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L)
  (And
     (LE_le_inst1 Nat instLENat
        (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
           inst_3
           inst_6
           inst_12 ts L)
        (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf Pi _UU03b3_ L))
     (LE_le_inst1 Nat instLENat
        (Prosa_Analysis_Definitions_BusyInterval_EdfPiBound_longest_busy_interval_with_pi Task
           inst_3
           inst_6
           inst_9
           (Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model Task
              inst_3
              inst_6)
           inst_12 ts tsk)
        (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf Pi _UU03b3_ L)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Results_Rta_Prm_Edf_FullyNonpreemptive_busy_window_recurrence_solution 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts tsk Pi _UU03b3_ L
```
