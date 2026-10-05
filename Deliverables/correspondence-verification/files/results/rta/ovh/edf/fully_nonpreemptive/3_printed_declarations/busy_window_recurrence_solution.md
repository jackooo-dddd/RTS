# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ovh.edf.fully_nonpreemptive.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Ovh.Edf.FullyNonpreemptive.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
MaxArrivals Task ->
seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> duration -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H0 H1} ts%seq_scope tsk DB CSB CRPDB L
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.ovh.edf.fully_nonpreemptive.busy_window_recurrence_solution
Declared in library prosa.results.rta.ovh.edf.fully_nonpreemptive, line 152, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> duration -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (DB CSB CRPDB : duration) =>
let overhead_bound :=
  fun Δ : duration => (DB + CSB + CRPDB) * (1 + 2 * (\sum_(tsk_o <- ts) @max_arrivals Task H1 tsk_o Δ)) in
fun L : duration =>
is_true (0 < L) /\
is_true (overhead_bound L + @total_request_bound_function Task H H1 ts L <= L) /\
is_true
  (overhead_bound L +
   @longest_busy_interval_with_pi Task H H0 (@fully_nonpreemptive_task_model Task H) H1 ts tsk <= L)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> duration -> Prop

Arguments busy_window_recurrence_solution {Task H H0 H1} ts%seq_scope tsk DB CSB CRPDB L
```

## Lean

```lean
@Prosa.Results.Rta.Ovh.Edf.FullyNonpreemptive.busy_window_recurrence_solution : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          List Task →
            Task →
              Prosa.Behavior.Time.duration →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Results.Rta.Ovh.Edf.FullyNonpreemptive.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          List Task →
            Task →
              Prosa.Behavior.Time.duration →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts tsk DB CSB CRPDB L =>
  have overhead_bound := fun Δ =>
    (DB + CSB + CRPDB) *
      (1 + 2 * Prosa.Util.Sum.sumSeq ts fun tsk_o => Prosa.Model.Task.Arrival.Curves.max_arrivals tsk_o Δ);
  0 < L ∧
    overhead_bound L + Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L ≤ L ∧
      overhead_bound L + Prosa.Analysis.Definitions.BusyInterval.EdfPiBound.longest_busy_interval_with_pi ts tsk ≤ L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ovh_Edf_FullyNonpreemptive_busy_window_recurrence_solution
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
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Results_Rta_Ovh_Edf_FullyNonpreemptive_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0
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
  (ts : List Task) (tsk : Task) (DB CSB CRPDB L : Prosa_Behavior_Time_duration) =>
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
          (Prosa_Util_Sum_sumSeq Task ts
             (fun tsk_o : Task =>
              Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                inst_3
                inst_12 tsk_o
                _UU0394_))))
  in
And
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L)
  (And
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (overhead_bound L)
           (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
              inst_3
              inst_6
              inst_12 ts L))
        L)
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (overhead_bound L)
           (Prosa_Analysis_Definitions_BusyInterval_EdfPiBound_longest_busy_interval_with_pi Task
              inst_3
              inst_6
              inst_9
              (Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model Task
                 inst_3
                 inst_6)
              inst_12 ts tsk))
        L))
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
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Results_Rta_Ovh_Edf_FullyNonpreemptive_busy_window_recurrence_solution 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts tsk DB DB CSB CRPDB
```
