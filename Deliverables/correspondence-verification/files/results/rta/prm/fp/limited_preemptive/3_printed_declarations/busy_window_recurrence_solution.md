# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.prm.fp.limited_preemptive.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Prm.Fp.LimitedPreemptive.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
TaskPreemptionPoints Task ->
seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> duration -> duration -> duration -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H0 H1} ts%seq_scope tsk {FP} Π γ L
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.prm.fp.limited_preemptive.busy_window_recurrence_solution
Declared in library prosa.results.rta.prm.fp.limited_preemptive, line 144, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       TaskPreemptionPoints Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> FP_policy Task -> duration -> duration -> duration -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : TaskPreemptionPoints Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (FP : FP_policy Task) 
  (Π γ L : duration) =>
is_true (0 < L) /\
is_true
  (@blocking_bound Task (@TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task H1) FP ts tsk +
   @total_hep_request_bound_function_FP Task H H0 ts FP tsk L <= prm_sbf Π γ L)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       TaskPreemptionPoints Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> FP_policy Task -> duration -> duration -> duration -> Prop

Arguments busy_window_recurrence_solution {Task H H0 H1} ts%seq_scope tsk {FP} Π γ L
```

## Lean

```lean
@Prosa.Results.Rta.Prm.Fp.LimitedPreemptive.busy_window_recurrence_solution : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
          List Task →
            Task →
              [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Results.Rta.Prm.Fp.LimitedPreemptive.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
          List Task →
            Task →
              [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] ts tsk
    [Prosa.Model.Priority.Definitions.FP_policy Task] Pi γ L =>
  0 < L ∧
    Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk +
        Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk L ≤
      Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf Pi γ L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Prm_Fp_LimitedPreemptive_busy_window_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Results_Rta_Prm_Fp_LimitedPreemptive_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
     inst_3)
  (ts : List Task) (tsk : Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (Pi _UU03b3_ L : Prosa_Behavior_Time_duration) =>
And
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L)
  (LE_le_inst1 Nat instLENat
     (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
        (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
           inst_3
           (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
              Task inst_3
              inst_12)
           FP ts tsk)
        (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
           inst_3
           inst_6
           inst_9 ts FP tsk L))
     (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf Pi _UU03b3_ L))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Results_Rta_Prm_Fp_LimitedPreemptive_busy_window_recurrence_solution 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts tsk FP Pi _UU03b3_ L
```
