# `is_in_concrete_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.fifo.bounded_nps.is_in_concrete_search_space`
- Lean: `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space`
- Certificate: `is_in_concrete_search_space_correspondence`

## Official Rocq

```coq
is_in_concrete_search_space :
forall {Task : TaskType},
TaskCost Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> bool

is_in_concrete_search_space is not universe polymorphic
Arguments is_in_concrete_search_space {Task H H0} ts%seq_scope L A
is_in_concrete_search_space is transparent
Expands to: Constant prosa.results.rta.ideal.fifo.bounded_nps.is_in_concrete_search_space
Declared in library prosa.results.rta.ideal.fifo.bounded_nps, line 320, characters 13-40
@is_in_concrete_search_space
     : forall Task : TaskType,
       TaskCost Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> bool
```

Body:

```coq
is_in_concrete_search_space =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (L A : duration) =>
(A < L) &&
@has (Equality.sort Task)
  (fun tsk' : Equality.sort Task =>
   @task_request_bound_function Task H H0 tsk' A != @task_request_bound_function Task H H0 tsk' (A + 1))
  ts
     : forall {Task : TaskType},
       TaskCost Task -> MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> bool

Arguments is_in_concrete_search_space {Task H H0} ts%seq_scope L A
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts L A =>
  decide (A < L) &&
    ts.any fun tsk' =>
      decide
        (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk' A ≠
          Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk' (A + 1))
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_is_in_concrete_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_is_in_concrete_search_space@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_13 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (L A : Prosa_Behavior_Time_duration) =>
Bool_and (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat A L) (Nat_decLt A L))
  (List_any Task ts
     (fun tsk' : Task =>
      Decidable_decide
        (Ne Nat
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_10
              inst_13 tsk' A)
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_10
              inst_13 tsk'
              (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                 Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
        (instDecidableNot
           (@eq Nat
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_10
                 inst_13 tsk' A)
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_10
                 inst_13 tsk'
                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
           (instDecidableEqNat
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_10
                 inst_13 tsk' A)
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_10
                 inst_13 tsk'
                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Results_Rta_Ideal_Fifo_BoundedNps_is_in_concrete_search_space Task
  inst_3
  inst_10
  inst_13 ts 
  L R
```
