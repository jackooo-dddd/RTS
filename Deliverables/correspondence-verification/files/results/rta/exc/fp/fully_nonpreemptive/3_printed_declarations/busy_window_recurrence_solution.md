# `busy_window_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.exc.fp.fully_nonpreemptive.busy_window_recurrence_solution`
- Lean: `Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive.busy_window_recurrence_solution`
- Certificate: `busy_window_recurrence_solution_correspondence`

## Official Rocq

```coq
busy_window_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task -> seq (Equality.sort Task) -> FP_policy Task -> work -> Equality.sort Task -> nat -> Prop

busy_window_recurrence_solution is not universe polymorphic
Arguments busy_window_recurrence_solution {Task H H0} ts%seq_scope {FP} e tsk L%nat_scope
busy_window_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.exc.fp.fully_nonpreemptive.busy_window_recurrence_solution
Declared in library prosa.results.rta.exc.fp.fully_nonpreemptive, line 79, characters 13-44
@busy_window_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> FP_policy Task -> work -> Equality.sort Task -> nat -> Prop
```

Body:

```coq
busy_window_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (FP : FP_policy Task) (e : work) (tsk : Equality.sort Task) (L : nat) =>
is_true (e < L) /\
is_true
  (@blocking_bound Task (@fully_nonpreemptive_task_model Task H) FP ts tsk +
   @total_hep_request_bound_function_FP Task H H0 ts FP tsk L + e <= L)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> FP_policy Task -> work -> Equality.sort Task -> nat -> Prop

Arguments busy_window_recurrence_solution {Task H H0} ts%seq_scope {FP} e tsk L%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive.busy_window_recurrence_solution : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Prosa.Behavior.Job.work → Task → ℕ → Prop
```

Body:

```lean
def Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive.busy_window_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task →
          [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Prosa.Behavior.Job.work → Task → ℕ → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts [Prosa.Model.Priority.Definitions.FP_policy Task] e tsk L =>
  e < L ∧
    Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk +
          Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk L +
        e ≤
      L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_busy_window_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Job_work -> Task -> Nat -> SProp
```

Body:

```coq
Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_busy_window_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (e : Prosa_Behavior_Job_work) (tsk : Task) (L : Nat) =>
And (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat e L)
  (LE_le_inst1 Nat instLENat
     (HAdd_hAdd_inst7 Nat Prosa_Behavior_Job_work Nat (instHAdd_inst1 Nat instAddNat)
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
        e)
     L)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Behavior_Job_work -> Task -> Nat -> SProp

Arguments Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_busy_window_recurrence_solution 
  Task inst_3
  inst_6
  inst_9 
  ts FP e tsk x____at___Init_Prelude3715277255__hygCtx13_Init_Prelude3715277255__hygCtx__hyg24%_Nat_scope
```
