# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.arm.edf.floating_nonpreemptive.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Arm.Edf.FloatingNonpreemptive.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
MaxArrivals Task ->
TaskMaxNonpreemptiveSegment Task ->
seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> duration -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H0 H1 H2} ts%seq_scope tsk Π Θ ν L
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.arm.edf.floating_nonpreemptive.busy_window_recurrence_solution
Declared in library prosa.results.rta.arm.edf.floating_nonpreemptive, line 140, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> duration -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
  (H2 : TaskMaxNonpreemptiveSegment Task) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task)
  (Π Θ ν L : duration) =>
is_true (0 < L) /\
is_true (@total_request_bound_function Task H H1 ts L <= arm_sbf Π Θ ν L) /\
is_true (@longest_busy_interval_with_pi Task H H0 H2 H1 ts tsk <= arm_sbf Π Θ ν L)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> duration -> Prop

Arguments busy_window_recurrence_solution {Task H H0 H1 H2} ts%seq_scope tsk Π Θ ν L
```

## Lean

```lean
@Prosa.Results.Rta.Arm.Edf.FloatingNonpreemptive.busy_window_recurrence_solution : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
            List Task →
              Task →
                Prosa.Behavior.Time.duration →
                  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Results.Rta.Arm.Edf.FloatingNonpreemptive.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
            List Task →
              Task →
                Prosa.Behavior.Time.duration →
                  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] ts tsk Pi Θ ν L =>
  0 < L ∧
    Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L ≤
        Prosa.Analysis.Definitions.Sbf.Average.arm_sbf Pi Θ ν L ∧
      Prosa.Analysis.Definitions.BusyInterval.EdfPiBound.longest_busy_interval_with_pi ts tsk ≤
        Prosa.Analysis.Definitions.Sbf.Average.arm_sbf Pi Θ ν L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Arm_Edf_FloatingNonpreemptive_busy_window_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Results_Rta_Arm_Edf_FloatingNonpreemptive_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0
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
  (inst_15 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (ts : List Task) (tsk : Task) (Pi _UU0398_ _UU03bd_ L : Prosa_Behavior_Time_duration) =>
And
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L)
  (And
     (LE_le_inst1 Nat instLENat
        (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
           inst_3
           inst_6
           inst_12 ts L)
        (Prosa_Analysis_Definitions_Sbf_Average_arm_sbf Pi _UU0398_ _UU03bd_ L))
     (LE_le_inst1 Nat instLENat
        (Prosa_Analysis_Definitions_BusyInterval_EdfPiBound_longest_busy_interval_with_pi Task
           inst_3
           inst_6
           inst_9
           inst_15
           inst_12 ts tsk)
        (Prosa_Analysis_Definitions_Sbf_Average_arm_sbf Pi _UU0398_ _UU03bd_ L)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Results_Rta_Arm_Edf_FloatingNonpreemptive_busy_window_recurrence_solution 
  Task inst_3
  inst_6
  inst_9
  inst_12
  inst_15 
  ts tsk Pi _UU0398_ _UU03bd_ L
```
