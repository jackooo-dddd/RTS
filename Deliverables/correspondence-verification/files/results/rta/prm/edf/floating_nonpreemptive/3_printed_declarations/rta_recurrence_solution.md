# `rta_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.prm.edf.floating_nonpreemptive.rta_recurrence_solution`
- Lean: `Prosa.Results.Rta.Prm.Edf.FloatingNonpreemptive.rta_recurrence_solution`
- Certificate: `rta_recurrence_solution_correspondence`

## Official Rocq

```coq
rta_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
MaxArrivals Task ->
TaskMaxNonpreemptiveSegment Task ->
seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> nat -> Prop

rta_recurrence_solution is not universe polymorphic
Arguments rta_recurrence_solution {Task H H0 H1 H2} ts%seq_scope tsk Π γ L R%nat_scope
rta_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.prm.edf.floating_nonpreemptive.rta_recurrence_solution
Declared in library prosa.results.rta.prm.edf.floating_nonpreemptive, line 154, characters 13-36
@rta_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> nat -> Prop
```

Body:

```coq
rta_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
  (H2 : TaskMaxNonpreemptiveSegment Task) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task)
  (Π γ L : duration) (R : nat) =>
forall A : duration,
is_true (@is_in_search_space Task H H0 H2 ts H1 tsk L A) ->
exists F : duration,
  is_true
    (@blocking_bound Task H H0 H2 ts H1 tsk A + @task_request_bound_function Task H H1 tsk (A + 1) +
     @bound_on_athep_workload Task H H0 H1 ts tsk A F <= prm_sbf Π γ F) /\
  is_true (F <= A + R)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> nat -> Prop

Arguments rta_recurrence_solution {Task H H0 H1 H2} ts%seq_scope tsk Π γ L R%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Prm.Edf.FloatingNonpreemptive.rta_recurrence_solution : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
            List Task →
              Task →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ → Prop
```

Body:

```lean
def Prosa.Results.Rta.Prm.Edf.FloatingNonpreemptive.rta_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
            List Task →
              Task →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] ts tsk Pi γ L R =>
  ∀ (A : Prosa.Behavior.Time.duration),
    Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf.is_in_search_space ts tsk L A = true →
      ∃ F,
        Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk A +
                Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) +
              Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload ts tsk A F ≤
            Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf Pi γ F ∧
          F ≤ A + R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Prm_Edf_FloatingNonpreemptive_rta_recurrence_solution
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
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat -> SProp
```

Body:

```coq
Prosa_Results_Rta_Prm_Edf_FloatingNonpreemptive_rta_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (ts : List Task) (tsk : Task) (Pi _UU03b3_ L : Prosa_Behavior_Time_duration) (R : Nat) =>
forall A : Prosa_Behavior_Time_duration,
@eq Bool
  (Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Edf_is_in_search_space Task
     inst_3
     inst_6
     inst_9
     inst_15 ts
     inst_12 tsk L A)
  Bool_true ->
Exists Prosa_Behavior_Time_duration
  (fun F : Prosa_Behavior_Time_duration =>
   And
     (LE_le_inst1 Nat instLENat
        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
           (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
              (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                 inst_3
                 inst_6
                 inst_9
                 inst_15 ts
                 inst_12 tsk A)
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_6
                 inst_12 tsk
                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
           (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
              inst_3
              inst_6
              inst_9
              inst_12 ts tsk A F))
        (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf Pi _UU03b3_ F))
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat F
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))
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
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat -> SProp

Arguments Prosa_Results_Rta_Prm_Edf_FloatingNonpreemptive_rta_recurrence_solution 
  Task inst_3
  inst_6
  inst_9
  inst_12
  inst_15 
  ts tsk Pi _UU03b3_ L
  x____at___Init_Prelude3715277255__hygCtx13_Init_Prelude3715277255__hygCtx__hyg24%_Nat_scope
```
