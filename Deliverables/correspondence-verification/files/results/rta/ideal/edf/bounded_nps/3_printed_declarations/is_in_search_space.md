# `is_in_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space`
- Lean: `Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space`
- Certificate: `is_in_search_space_correspondence`

## Official Rocq

```coq
is_in_search_space :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> duration -> bool

is_in_search_space is not universe polymorphic
Arguments is_in_search_space {Task H H0} ts%seq_scope {H5} tsk L A
is_in_search_space is transparent
Expands to: Constant prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space
Declared in library prosa.results.rta.ideal.edf.bounded_nps, line 128, characters 13-31
@is_in_search_space
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> duration -> bool
```

Body:

```coq
is_in_search_space =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (ts : seq (Equality.sort Task))
  (H5 : MaxArrivals Task) (tsk : Equality.sort Task) (L A : duration) =>
(A < L) &&
(@task_rbf_changes_at Task H H5 tsk A || @bound_on_total_hep_workload_changes_at Task H H0 ts H5 tsk A)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> duration -> bool

Arguments is_in_search_space {Task H H0} ts%seq_scope {H5} tsk L A
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        List Task →
          [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
            Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        List Task →
          [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
            Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task] ts
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk L A =>
  decide (A < L) &&
    (Prosa.Results.Rta.Ideal.Edf.BoundedPi.task_rbf_changes_at tsk A ||
      Prosa.Results.Rta.Ideal.Edf.BoundedPi.bound_on_total_hep_workload_changes_at ts tsk A)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (tsk : Task) (L A : Prosa_Behavior_Time_duration) =>
Bool_and (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat A L) (Nat_decLt A L))
  (Bool_or
     (Prosa_Results_Rta_Ideal_Edf_BoundedPi_task_rbf_changes_at Task
        inst_3
        inst_10
        inst_18 tsk A)
     (Prosa_Results_Rta_Ideal_Edf_BoundedPi_bound_on_total_hep_workload_changes_at Task
        inst_3
        inst_10
        inst_13 ts
        inst_18 tsk A))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space Task
  inst_3
  inst_10
  inst_13 ts
  inst_18 tsk 
  L R
```
