# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.rs.fp.fully_nonpreemptive.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Rs.Fp.FullyNonpreemptive.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> SupplyBoundFunction -> duration -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H0} ts%seq_scope tsk {FP SBF} L
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.rs.fp.fully_nonpreemptive.busy_window_recurrence_solution
Declared in library prosa.results.rta.rs.fp.fully_nonpreemptive, line 151, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> FP_policy Task -> SupplyBoundFunction -> duration -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task) (FP : FP_policy Task) (SBF : SupplyBoundFunction) (L : duration) =>
is_true (0 < L) /\
is_true
  (@blocking_bound Task (@fully_nonpreemptive_task_model Task H) FP ts tsk +
   @total_hep_request_bound_function_FP Task H H0 ts FP tsk L <= SBF L)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> FP_policy Task -> SupplyBoundFunction -> duration -> Prop

Arguments busy_window_recurrence_solution {Task H H0} ts%seq_scope tsk {FP SBF} L
```

## Lean

```lean
@Prosa.Results.Rta.Rs.Fp.FullyNonpreemptive.busy_window_recurrence_solution : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task →
          Task →
            [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
              Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Results.Rta.Rs.Fp.FullyNonpreemptive.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task →
          Task →
            [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
              Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts tsk [Prosa.Model.Priority.Definitions.FP_policy Task] SBF L =>
  0 < L ∧
    Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk +
        Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk L ≤
      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Rs_Fp_FullyNonpreemptive_busy_window_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Results_Rta_Rs_Fp_FullyNonpreemptive_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (tsk : Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) (L : Prosa_Behavior_Time_duration) =>
And
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L)
  (LE_le_inst1 Nat instLENat
     (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
        (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
           inst_3
           (Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model Task
              inst_3
              inst_6)
           FP ts tsk)
        (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
           inst_3
           inst_6
           inst_9 ts FP tsk L))
     (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF L))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Results_Rta_Rs_Fp_FullyNonpreemptive_busy_window_recurrence_solution 
  Task inst_3
  inst_6
  inst_9 
  ts tsk FP SBF L
```
