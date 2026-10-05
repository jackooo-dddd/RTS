# `is_in_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.gel.bounded_pi.is_in_search_space`
- Lean: `Prosa.Results.Rta.Ideal.Gel.BoundedPi.is_in_search_space`
- Certificate: `is_in_search_space_correspondence`

## Official Rocq

```coq
is_in_search_space :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
gel.PriorityPoint Task ->
seq (Equality.sort Task) -> Equality.sort Task -> (duration -> duration) -> duration -> duration -> bool

is_in_search_space is not universe polymorphic
Arguments is_in_search_space {Task H H2 H5} ts%seq_scope tsk priority_inversion_bound%function_scope L A
is_in_search_space is transparent
Expands to: Constant prosa.results.rta.ideal.gel.bounded_pi.is_in_search_space
Declared in library prosa.results.rta.ideal.gel.bounded_pi, line 273, characters 13-31
@is_in_search_space
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       gel.PriorityPoint Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> (duration -> duration) -> duration -> duration -> bool
```

Body:

```coq
is_in_search_space =
fun (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (H5 : gel.PriorityPoint Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task)
  (priority_inversion_bound : duration -> duration) (L : duration) =>
let interval :=
  fun (tsk_o : Equality.sort Task) (A : instant) =>
  @ssralg.GRing.add
    (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
       ssrint.ssrint_int__canonical__GRing_PzSemiRing)
    (@ssralg.GRing.add
       (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
          ssrint.ssrint_int__canonical__GRing_PzSemiRing)
       (@ssralg.GRing.natmul
          (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
             ssrint.ssrint_int__canonical__GRing_PzSemiRing)
          (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) (A + 1))
       (@gel.task_priority_point Task H5 tsk))
    (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule (@gel.task_priority_point Task H5 tsk_o))
  in
fun A : duration =>
(A < L) &&
(priority_inversion_changes_at priority_inversion_bound A || @task_rbf_changes_at Task H H2 tsk A
 || @bound_on_total_hep_workload_changes_at Task H5 ts tsk A)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       gel.PriorityPoint Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> (duration -> duration) -> duration -> duration -> bool

Arguments is_in_search_space {Task H H2 H5} ts%seq_scope tsk priority_inversion_bound%function_scope L A
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Gel.BoundedPi.is_in_search_space : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            Task →
              (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Gel.BoundedPi.is_in_search_space.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            Task →
              (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] ts tsk
    priority_inversion_bound L A =>
  decide (A < L) &&
    (Prosa.Results.Rta.Ideal.Gel.BoundedPi.priority_inversion_changes_at priority_inversion_bound A ||
        Prosa.Results.Rta.Ideal.Gel.BoundedPi.task_rbf_changes_at tsk A ||
      Prosa.Results.Rta.Ideal.Gel.BoundedPi.bound_on_total_hep_workload_changes_at ts tsk A)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_is_in_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Task ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_is_in_search_space@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_13 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (inst_16 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (ts : List Task) (tsk : Task)
  (priority_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
  (L A : Prosa_Behavior_Time_duration) =>
Bool_and (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat A L) (Nat_decLt A L))
  (Bool_or
     (Bool_or
        (Prosa_Results_Rta_Ideal_Gel_BoundedPi_priority_inversion_changes_at priority_inversion_bound A)
        (Prosa_Results_Rta_Ideal_Gel_BoundedPi_task_rbf_changes_at Task
           inst_3
           inst_10
           inst_13 tsk A))
     (Prosa_Results_Rta_Ideal_Gel_BoundedPi_bound_on_total_hep_workload_changes_at Task
        inst_3
        inst_16 ts tsk A))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Task ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Results_Rta_Ideal_Gel_BoundedPi_is_in_search_space Task
  inst_3
  inst_10
  inst_13
  inst_16 ts 
  tsk priority_inversion_bound%_function_scope L R
```
