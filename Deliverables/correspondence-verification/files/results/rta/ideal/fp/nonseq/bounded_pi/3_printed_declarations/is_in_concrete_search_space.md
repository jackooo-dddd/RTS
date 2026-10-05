# `is_in_concrete_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.fp.nonseq.bounded_pi.is_in_concrete_search_space`
- Lean: `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.is_in_concrete_search_space`
- Certificate: `is_in_concrete_search_space_correspondence`

## Official Rocq

```coq
is_in_concrete_search_space :
forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat -> bool

is_in_concrete_search_space is not universe polymorphic
Arguments is_in_concrete_search_space {Task H MaxArrivals0} tsk L A%nat_scope
is_in_concrete_search_space is transparent
Expands to: Constant prosa.results.rta.ideal.fp.nonseq.bounded_pi.is_in_concrete_search_space
Declared in library prosa.results.rta.ideal.fp.nonseq.bounded_pi, line 317, characters 15-42
@is_in_concrete_search_space
     : forall Task : TaskType,
       TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat -> bool
```

Body:

```coq
is_in_concrete_search_space =
fun (Task : TaskType) (H : TaskCost Task) (MaxArrivals0 : MaxArrivals Task) (tsk : Equality.sort Task) =>
let task_rbf := @task_request_bound_function Task H MaxArrivals0 tsk in
fun (L : duration) (A : nat) => (A < L) && (task_rbf A != task_rbf (A + 1))
     : forall {Task : TaskType},
       TaskCost Task -> MaxArrivals Task -> Equality.sort Task -> duration -> nat -> bool

Arguments is_in_concrete_search_space {Task H MaxArrivals0} tsk L A%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.is_in_concrete_search_space : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → ℕ → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.is_in_concrete_search_space.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → ℕ → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk L A =>
  decide (A < L) &&
    decide
      (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk A ≠
        Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1))
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_is_in_concrete_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_is_in_concrete_search_space@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
  (inst_13 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
  (tsk : Task) (L : Prosa_Behavior_Time_duration) (A : Nat) =>
Bool_and (Decidable_decide (LT_lt_inst1 Nat instLTNat A L) (Nat_decLt A L))
  (Decidable_decide
     (Ne Nat
        (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
           inst_3
           inst_10
           inst_13 tsk A)
        (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
           inst_3
           inst_10
           inst_13 tsk
           (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
     (instDecidableNot
        (@eq Nat
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_10
              inst_13 tsk A)
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_10
              inst_13 tsk
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
        (instDecidableEqNat
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_10
              inst_13 tsk A)
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_10
              inst_13 tsk
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat -> Bool

Arguments Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_is_in_concrete_search_space 
  Task inst_3
  inst_10
  inst_13 tsk 
  L x____at___Init_Prelude2408276647__hygCtx__hyg14%_Nat_scope
```
