# `is_in_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.restricted_supply.search_space.edf.is_in_search_space`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf.is_in_search_space`
- Certificate: `is_in_search_space_correspondence`

## Official Rocq

```coq
is_in_search_space :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
TaskMaxNonpreemptiveSegment Task ->
seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> duration -> bool

is_in_search_space is not universe polymorphic
Arguments is_in_search_space {Task H H0 H1} ts%seq_scope {H2} tsk L A
is_in_search_space is transparent
Expands to: Constant prosa.analysis.abstract.restricted_supply.search_space.edf.is_in_search_space
Declared in library prosa.analysis.abstract.restricted_supply.search_space.edf, line 82, characters 13-31
@is_in_search_space
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> duration -> bool
```

Body:

```coq
is_in_search_space =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : TaskMaxNonpreemptiveSegment Task)
  (ts : seq (Equality.sort Task)) (H2 : MaxArrivals Task) (tsk : Equality.sort Task) 
  (L : duration) =>
let D := [eta @task_deadline Task H0] in
let rbf := @task_request_bound_function Task H H2 in
let task_rbf_changes_at := fun A : duration => rbf tsk A != rbf tsk (A + 1) in
let bound_on_total_hep_workload_changes_at :=
  fun A : duration =>
  let new_hep_job_released_by :=
    fun tsko : Equality.sort Task =>
    (tsk != tsko) && (rbf tsko (A + D tsk - D tsko) != rbf tsko (A + 1 + D tsk - D tsko)) in
  @has (Equality.sort Task) new_hep_job_released_by ts in
let blocking_bound_changes_at :=
  fun A : duration =>
  @blocking_bound Task H H0 H1 ts H2 tsk (A - 1) != @blocking_bound Task H H0 H1 ts H2 tsk A in
fun A : duration =>
(A < L) && (blocking_bound_changes_at A || task_rbf_changes_at A || bound_on_total_hep_workload_changes_at A)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> duration -> bool

Arguments is_in_search_space {Task H H0 H1} ts%seq_scope {H2} tsk L A
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf.is_in_search_space : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
          List Task →
            [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
              Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool
```

Body:

```lean
def Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf.is_in_search_space.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
          List Task →
            [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
              Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] ts
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk L A =>
  decide (A < L) &&
    (decide
          (Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk (A - 1) ≠
            Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk A) ||
        decide
          (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk A ≠
            Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1)) ||
      ts.any fun tsko =>
        decide (tsk ≠ tsko) &&
          decide
            (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko
                (A + Prosa.Model.Task.Concept.task_deadline tsk - Prosa.Model.Task.Concept.task_deadline tsko) ≠
              Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko
                (A + 1 + Prosa.Model.Task.Concept.task_deadline tsk - Prosa.Model.Task.Concept.task_deadline tsko)))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Edf_is_in_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Edf_is_in_search_space@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Concept_TaskDeadline Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (ts : List Task)
  (inst_17 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (L A : Prosa_Behavior_Time_duration) =>
Bool_and (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat A L) (Nat_decLt A L))
  (Bool_or
     (Bool_or
        (Decidable_decide
           (Ne Nat
              (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                 inst_3
                 inst_6
                 inst_9
                 inst_12
                 ts
                 inst_17
                 tsk
                 (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
              (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                 inst_3
                 inst_6
                 inst_9
                 inst_12
                 ts
                 inst_17
                 tsk A))
           (instDecidableNot
              (@eq Nat
                 (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                    inst_3
                    inst_6
                    inst_9
                    inst_12
                    ts
                    inst_17
                    tsk
                    (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                       Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                       A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                 (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                    inst_3
                    inst_6
                    inst_9
                    inst_12
                    ts
                    inst_17
                    tsk A))
              (instDecidableEqNat
                 (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                    inst_3
                    inst_6
                    inst_9
                    inst_12
                    ts
                    inst_17
                    tsk
                    (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                       Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                       A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                 (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                    inst_3
                    inst_6
                    inst_9
                    inst_12
                    ts
                    inst_17
                    tsk A))))
        (Decidable_decide
           (Ne Nat
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_6
                 inst_17
                 tsk A)
              (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                 inst_3
                 inst_6
                 inst_17
                 tsk
                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
           (instDecidableNot
              (@eq Nat
                 (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                    inst_3
                    inst_6
                    inst_17
                    tsk A)
                 (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                    inst_3
                    inst_6
                    inst_17
                    tsk
                    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                       Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                       A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
              (instDecidableEqNat
                 (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                    inst_3
                    inst_6
                    inst_17
                    tsk A)
                 (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                    inst_3
                    inst_6
                    inst_17
                    tsk
                    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                       Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                       A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))))))
     (List_any Task ts
        (fun tsko : Task =>
         Bool_and
           (Decidable_decide (Ne Task tsk tsko)
              (instDecidableNot (@eq Task tsk tsko)
                 (inst_3
                    tsk tsko)))
           (Decidable_decide
              (Ne Nat
                 (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                    inst_3
                    inst_6
                    inst_17
                    tsko
                    (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                       Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                       (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                          Prosa_Behavior_Time_duration
                          (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                             inst_3
                             inst_9
                             tsk))
                       (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                          inst_3
                          inst_9
                          tsko)))
                 (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                    inst_3
                    inst_6
                    inst_17
                    tsko
                    (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                       Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                       (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                          Prosa_Behavior_Time_duration
                          (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                          (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                             Prosa_Behavior_Time_duration
                             (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                             (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
                          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                             inst_3
                             inst_9
                             tsk))
                       (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                          inst_3
                          inst_9
                          tsko))))
              (instDecidableNot
                 (@eq Nat
                    (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                       inst_3
                       inst_6
                       inst_17
                       tsko
                       (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                          Prosa_Behavior_Time_duration
                          (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                          (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                             Prosa_Behavior_Time_duration
                             (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                             (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                                inst_3
                                inst_9
                                tsk))
                          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                             inst_3
                             inst_9
                             tsko)))
                    (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                       inst_3
                       inst_6
                       inst_17
                       tsko
                       (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                          Prosa_Behavior_Time_duration
                          (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                          (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                             Prosa_Behavior_Time_duration
                             (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                             (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                                Prosa_Behavior_Time_duration
                                (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                                (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
                             (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                                inst_3
                                inst_9
                                tsk))
                          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                             inst_3
                             inst_9
                             tsko))))
                 (instDecidableEqNat
                    (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                       inst_3
                       inst_6
                       inst_17
                       tsko
                       (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                          Prosa_Behavior_Time_duration
                          (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                          (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                             Prosa_Behavior_Time_duration
                             (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                             (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                                inst_3
                                inst_9
                                tsk))
                          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                             inst_3
                             inst_9
                             tsko)))
                    (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                       inst_3
                       inst_6
                       inst_17
                       tsko
                       (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                          Prosa_Behavior_Time_duration
                          (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                          (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                             Prosa_Behavior_Time_duration
                             (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                             (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                                Prosa_Behavior_Time_duration
                                (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                                (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
                             (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                                inst_3
                                inst_9
                                tsk))
                          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                             inst_3
                             inst_9
                             tsko)))))))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Edf_is_in_search_space 
  Task inst_3
  inst_6
  inst_9
  inst_12 
  ts inst_17 
  tsk L R
```
