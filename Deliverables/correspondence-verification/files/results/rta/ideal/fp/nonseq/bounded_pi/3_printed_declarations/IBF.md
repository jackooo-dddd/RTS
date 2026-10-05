# `IBF`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.fp.nonseq.bounded_pi.IBF`
- Lean: `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.IBF`
- Certificate: `IBF_correspondence`

## Official Rocq

```coq
IBF :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
FP_policy Task -> seq (Equality.sort Task) -> Equality.sort Task -> duration -> instant -> duration -> nat

IBF is not universe polymorphic
Arguments IBF {Task H MaxArrivals0 FP} ts%seq_scope tsk priority_inversion_bound A Δ
IBF is transparent
Expands to: Constant prosa.results.rta.ideal.fp.nonseq.bounded_pi.IBF
Declared in library prosa.results.rta.ideal.fp.nonseq.bounded_pi, line 148, characters 13-16
@IBF
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       FP_policy Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> instant -> duration -> nat
```

Body:

```coq
IBF =
fun (Task : TaskType) (H : TaskCost Task) (MaxArrivals0 : MaxArrivals Task) (FP : FP_policy Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (priority_inversion_bound : duration) =>
let task_rbf := @task_request_bound_function Task H MaxArrivals0 tsk in
let total_ohep_rbf := @total_ohep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk in
fun (A : instant) (Δ : duration) =>
priority_inversion_bound + (task_rbf (maxn (A + 1) Δ) - @task_cost Task H tsk) + total_ohep_rbf Δ
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       FP_policy Task ->
       seq (Equality.sort Task) -> Equality.sort Task -> duration -> instant -> duration -> nat

Arguments IBF {Task H MaxArrivals0 FP} ts%seq_scope tsk priority_inversion_bound A Δ
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.IBF : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
          List Task →
            Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.IBF.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
          List Task →
            Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [Prosa.Model.Priority.Definitions.FP_policy Task] ts tsk
    priority_inversion_bound A Δ =>
  priority_inversion_bound +
      (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (Nat.max (A + 1) Δ) -
        Prosa.Model.Task.Concept.task_cost tsk) +
    Prosa.Analysis.Definitions.RequestBoundFunction.total_ohep_request_bound_function_FP ts tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_IBF
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_IBF@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_13 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (ts : List Task) (tsk : Task) (priority_inversion_bound : Prosa_Behavior_Time_duration)
  (A : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration) =>
HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
  (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_bound
     (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
        (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
           inst_3
           inst_10
           inst_13 tsk
           (Nat_max
              (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                 (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) A
                 (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
              _UU0394_))
        (Prosa_Model_Task_Concept_TaskCost_task_cost Task
           inst_3
           inst_10 tsk)))
  (Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP Task
     inst_3
     inst_10
     inst_13 ts FP tsk _UU0394_)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_IBF Task
  inst_3
  inst_10
  inst_13 
  FP ts tsk priority_inversion_bound A a____at____internal__hyg0
```
