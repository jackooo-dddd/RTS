# `is_in_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.restricted_supply.search_space.fifo.is_in_search_space`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo.is_in_search_space`
- Certificate: `is_in_search_space_correspondence`

## Official Rocq

```coq
is_in_search_space :
forall {Task : TaskType},
TaskCost Task -> seq (Equality.sort Task) -> MaxArrivals Task -> duration -> duration -> bool

is_in_search_space is not universe polymorphic
Arguments is_in_search_space {Task H} ts%seq_scope {H0} L A
is_in_search_space is transparent
Expands to: Constant prosa.analysis.abstract.restricted_supply.search_space.fifo.is_in_search_space
Declared in library prosa.analysis.abstract.restricted_supply.search_space.fifo, line 59, characters 13-31
@is_in_search_space
     : forall Task : TaskType,
       TaskCost Task -> seq (Equality.sort Task) -> MaxArrivals Task -> duration -> duration -> bool
```

Body:

```coq
is_in_search_space =
fun (Task : TaskType) (H : TaskCost Task) (ts : seq (Equality.sort Task)) (H0 : MaxArrivals Task) =>
let rbf := [eta @task_request_bound_function Task H H0] in
fun L A : duration =>
let rbf_makes_a_step := fun tsk : Equality.sort Task => rbf tsk A != rbf tsk (A + 1) in
(A < L) && @has (Equality.sort Task) rbf_makes_a_step ts
     : forall {Task : TaskType},
       TaskCost Task -> seq (Equality.sort Task) -> MaxArrivals Task -> duration -> duration -> bool

Arguments is_in_search_space {Task H} ts%seq_scope {H0} L A
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo.is_in_search_space : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      List Task →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool
```

Body:

```lean
def Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo.is_in_search_space.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      List Task →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] ts
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] L A =>
  decide (A < L) &&
    ts.any fun tsk =>
      decide
        (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk A ≠
          Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fifo_is_in_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fifo_is_in_search_space@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (ts : List Task)
  (inst_11 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (L A : Prosa_Behavior_Time_duration) =>
Bool_and (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat A L) (Nat_decLt A L))
  (List_any Task ts
     (fun tsk : Task =>
      Decidable_decide
        (Ne Nat
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_6
              inst_11
              tsk A)
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_6
              inst_11
              tsk
              (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                 Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
        (instDecidableNot
           (@eq Nat
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_6
                 inst_11
                 tsk A)
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_6
                 inst_11
                 tsk
                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
           (instDecidableEqNat
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_6
                 inst_11
                 tsk A)
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_6
                 inst_11
                 tsk
                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fifo_is_in_search_space 
  Task inst_3
  inst_6 
  ts inst_11 
  L R
```
