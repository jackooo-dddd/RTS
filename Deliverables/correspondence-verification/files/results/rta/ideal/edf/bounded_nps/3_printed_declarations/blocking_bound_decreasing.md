# `blocking_bound_decreasing`

- Kind (Rocq): Fact
- Rocq: `prosa.results.rta.ideal.edf.bounded_nps.blocking_bound_decreasing`
- Lean: `Prosa.Results.Rta.Ideal.Edf.BoundedNps.blocking_bound_decreasing`
- Certificate: `blocking_bound_decreasing_correspondence`

## Official Rocq

```coq
blocking_bound_decreasing :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H2 : TaskMaxNonpreemptiveSegment Task}
  (ts : seq (Equality.sort Task)) {H5 : MaxArrivals Task} (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall A1 A2 : nat,
is_true (A1 <= A2) ->
is_true (@blocking_bound Task H H0 H2 ts H5 tsk A2 <= @blocking_bound Task H H0 H2 ts H5 tsk A1)

blocking_bound_decreasing is not universe polymorphic
Arguments blocking_bound_decreasing {Task H H0 H2} ts%seq_scope {H5} tsk H_tsk_in_ts (A1 A2)%nat_scope _
blocking_bound_decreasing is opaque
Expands to: Constant prosa.results.rta.ideal.edf.bounded_nps.blocking_bound_decreasing
Declared in library prosa.results.rta.ideal.edf.bounded_nps, line 134, characters 7-32
@blocking_bound_decreasing
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task)
         (H2 : TaskMaxNonpreemptiveSegment Task) (ts : seq (Equality.sort Task)) 
         (H5 : MaxArrivals Task) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall A1 A2 : nat,
       is_true (A1 <= A2) ->
       is_true (@blocking_bound Task H H0 H2 ts H5 tsk A2 <= @blocking_bound Task H H0 H2 ts H5 tsk A1)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.BoundedNps.blocking_bound_decreasing : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] (ts : List Task)
  [inst_4 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ (A1 A2 : ℕ),
      A1 ≤ A2 →
        Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk A2 ≤
          Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk A1
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedNps_blocking_bound_decreasing
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3)
         (ts : List Task)
         (inst_21 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       forall A1 A2 : Nat,
       LE_le_inst1 Nat instLENat A1 A2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
            inst_3
            inst_10
            inst_13
            inst_16 ts
            inst_21 tsk A2)
         (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
            inst_3
            inst_10
            inst_13
            inst_16 ts
            inst_21 tsk A1)
```
