# `bound_on_total_hep_workload_changes_at`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.edf.bounded_pi.bound_on_total_hep_workload_changes_at`
- Lean: `Prosa.Results.Rta.Ideal.Edf.BoundedPi.bound_on_total_hep_workload_changes_at`
- Certificate: `bound_on_total_hep_workload_changes_at_correspondence`

## Official Rocq

```coq
bound_on_total_hep_workload_changes_at :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task -> seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> nat -> bool

bound_on_total_hep_workload_changes_at is not universe polymorphic
Arguments bound_on_total_hep_workload_changes_at {Task H H0} ts%seq_scope {H5} tsk A%nat_scope
bound_on_total_hep_workload_changes_at is transparent
Expands to: Constant prosa.results.rta.ideal.edf.bounded_pi.bound_on_total_hep_workload_changes_at
Declared in library prosa.results.rta.ideal.edf.bounded_pi, line 178, characters 13-51
@bound_on_total_hep_workload_changes_at
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task -> seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> nat -> bool
```

Body:

```coq
bound_on_total_hep_workload_changes_at =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) =>
let D := [eta @task_deadline Task H0] in
fun (ts : seq (Equality.sort Task)) (H5 : MaxArrivals Task) (tsk : Equality.sort Task) =>
let rbf := @task_request_bound_function Task H H5 in
fun A : nat =>
@has (Equality.sort Task)
  (fun tsko : Equality.sort Task =>
   (tsk != tsko) && (rbf tsko (A + D tsk - D tsko) != rbf tsko (A + 1 + D tsk - D tsko)))
  ts
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task -> seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> nat -> bool

Arguments bound_on_total_hep_workload_changes_at {Task H H0} ts%seq_scope {H5} tsk A%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.BoundedPi.bound_on_total_hep_workload_changes_at : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        List Task → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → ℕ → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Edf.BoundedPi.bound_on_total_hep_workload_changes_at.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        List Task → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → ℕ → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task] ts
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk A =>
  ts.any fun tsko =>
    decide (tsk ≠ tsko) &&
      decide
        (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko
            (A + Prosa.Model.Task.Concept.task_deadline tsk - Prosa.Model.Task.Concept.task_deadline tsko) ≠
          Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko
            (A + 1 + Prosa.Model.Task.Concept.task_deadline tsk - Prosa.Model.Task.Concept.task_deadline tsko))
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedPi_bound_on_total_hep_workload_changes_at
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Nat -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedPi_bound_on_total_hep_workload_changes_at@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_13 : 
   Prosa_Model_Task_Concept_TaskDeadline Task
     inst_3)
  (ts : List Task)
  (inst_18 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (A : Nat) =>
List_any Task ts
  (fun tsko : Task =>
   Bool_and
     (Decidable_decide (Ne Task tsk tsko)
        (instDecidableNot (@eq Task tsk tsko)
           (inst_3 tsk tsko)))
     (Decidable_decide
        (Ne Nat
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_10
              inst_18 tsko
              (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                 (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                    (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                       inst_3
                       inst_13 tsk))
                 (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                    inst_3
                    inst_13 tsko)))
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_10
              inst_18 tsko
              (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                 (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                    (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                       (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
                    (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                       inst_3
                       inst_13 tsk))
                 (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                    inst_3
                    inst_13 tsko))))
        (instDecidableNot
           (@eq Nat
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_10
                 inst_18 tsko
                 (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                    (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                       (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                          inst_3
                          inst_13 tsk))
                    (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                       inst_3
                       inst_13 tsko)))
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_10
                 inst_18 tsko
                 (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                    (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                       (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                          A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
                       (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                          inst_3
                          inst_13 tsk))
                    (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                       inst_3
                       inst_13 tsko))))
           (instDecidableEqNat
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_10
                 inst_18 tsko
                 (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                    (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                       (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                          inst_3
                          inst_13 tsk))
                    (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                       inst_3
                       inst_13 tsko)))
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_10
                 inst_18 tsko
                 (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                    (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                       (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                          A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
                       (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                          inst_3
                          inst_13 tsk))
                    (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                       inst_3
                       inst_13 tsko)))))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Nat -> Bool

Arguments Prosa_Results_Rta_Ideal_Edf_BoundedPi_bound_on_total_hep_workload_changes_at 
  Task inst_3
  inst_10
  inst_13 ts
  inst_18 tsk
  x____at___Init_Prelude2408276647__hygCtx__hyg14%_Nat_scope
```
