# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ovh.fp.floating_nonpreemptive.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Ovh.Fp.FloatingNonpreemptive.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
TaskMaxNonpreemptiveSegment Task ->
seq (Equality.sort Task) ->
Equality.sort Task -> FP_policy Task -> duration -> duration -> duration -> duration -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H0 H1} ts%seq_scope tsk {FP} DB CSB CRPDB L
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.ovh.fp.floating_nonpreemptive.busy_window_recurrence_solution
Declared in library prosa.results.rta.ovh.fp.floating_nonpreemptive, line 171, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> FP_policy Task -> duration -> duration -> duration -> duration -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : TaskMaxNonpreemptiveSegment Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (FP : FP_policy Task) 
  (DB CSB CRPDB : duration) =>
let overhead_bound :=
  fun Δ : duration =>
  (DB + CSB + CRPDB) *
  (1 + 2 * (\sum_(tsk_o <- ts | @hep_task Task FP tsk_o tsk) @max_arrivals Task H0 tsk_o Δ)) in
fun L : duration =>
is_true (0 < L) /\
is_true
  (overhead_bound L + @blocking_bound Task H1 FP ts tsk +
   @total_hep_request_bound_function_FP Task H H0 ts FP tsk L <= L)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> FP_policy Task -> duration -> duration -> duration -> duration -> Prop

Arguments busy_window_recurrence_solution {Task H H0 H1} ts%seq_scope tsk {FP} DB CSB CRPDB L
```

## Lean

```lean
@Prosa.Results.Rta.Ovh.Fp.FloatingNonpreemptive.busy_window_recurrence_solution : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
          List Task →
            Task →
              [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
                Prosa.Behavior.Time.duration →
                  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Results.Rta.Ovh.Fp.FloatingNonpreemptive.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
          List Task →
            Task →
              [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
                Prosa.Behavior.Time.duration →
                  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] ts tsk
    [Prosa.Model.Priority.Definitions.FP_policy Task] DB CSB CRPDB L =>
  have overhead_bound := fun Δ =>
    (DB + CSB + CRPDB) *
      (1 +
        2 *
          Prosa.Util.Sum.sumFiltered ts (fun tsk_o => Prosa.Model.Priority.Definitions.hep_task tsk_o tsk) fun tsk_o =>
            Prosa.Model.Task.Arrival.Curves.max_arrivals tsk_o Δ);
  0 < L ∧
    overhead_bound L + Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk +
        Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk L ≤
      L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ovh_Fp_FloatingNonpreemptive_busy_window_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Results_Rta_Ovh_Fp_FloatingNonpreemptive_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (ts : List Task) (tsk : Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (DB CSB CRPDB L : Prosa_Behavior_Time_duration) =>
let overhead_bound :=
  fun _UU0394_ : Prosa_Behavior_Time_duration =>
  HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
       (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
       (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
          Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) DB CSB)
       CRPDB)
    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
       (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
       (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))
       (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
          (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
          (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 2 (instOfNatNat 2))
          (Prosa_Util_Sum_sumFiltered Task ts
             (fun tsk_o : Task =>
              Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
                inst_3 FP tsk_o
                tsk)
             (fun tsk_o : Task =>
              Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                inst_3
                inst_9 tsk_o
                _UU0394_))))
  in
And
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L)
  (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
        (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (overhead_bound L)
           (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
              inst_3
              inst_12 FP ts tsk))
        (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
           inst_3
           inst_6
           inst_9 ts FP tsk L))
     L)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Results_Rta_Ovh_Fp_FloatingNonpreemptive_busy_window_recurrence_solution 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts tsk FP DB DB CSB CRPDB
```
