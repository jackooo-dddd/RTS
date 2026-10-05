# `search_space_inclusion`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.edf.bounded_nps.search_space_inclusion`
- Lean: `Prosa.Results.Rta.Ideal.Edf.BoundedNps.search_space_inclusion`
- Certificate: `search_space_inclusion_correspondence`

## Official Rocq

```coq
search_space_inclusion :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H2 : TaskMaxNonpreemptiveSegment Task}
  (ts : seq (Equality.sort Task)) {H5 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall {A L : duration},
is_true (@bounded_pi.is_in_search_space Task H H0 ts H5 tsk (@blocking_bound Task H H0 H2 ts H5 tsk) L A) ->
is_true (@is_in_search_space Task H H0 ts H5 tsk L A)

search_space_inclusion is not universe polymorphic
Arguments search_space_inclusion {Task H H0 H2} ts%seq_scope {H5} H_valid_arrival_curve 
  tsk H_tsk_in_ts {A L} _
search_space_inclusion is opaque
Expands to: Constant prosa.results.rta.ideal.edf.bounded_nps.search_space_inclusion
Declared in library prosa.results.rta.ideal.edf.bounded_nps, line 173, characters 8-30
@search_space_inclusion
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task)
         (H2 : TaskMaxNonpreemptiveSegment Task) (ts : seq (Equality.sort Task)) 
         (H5 : MaxArrivals Task),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall A L : duration,
       is_true
         (@bounded_pi.is_in_search_space Task H H0 ts H5 tsk (@blocking_bound Task H H0 H2 ts H5 tsk) L A) ->
       is_true (@is_in_search_space Task H H0 ts H5 tsk L A)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.BoundedNps.search_space_inclusion : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] (ts : List Task)
  [inst_4 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (A L : Prosa.Behavior.Time.duration),
          Prosa.Results.Rta.Ideal.Edf.BoundedPi.is_in_search_space ts tsk
                (Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk) L A =
              true →
            Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space ts tsk L A = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedNps_search_space_inclusion
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
            inst_3),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_21) ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall A L : Prosa_Behavior_Time_duration,
       @eq Bool
         (Prosa_Results_Rta_Ideal_Edf_BoundedPi_is_in_search_space Task
            inst_3
            inst_10
            inst_13 ts
            inst_21 tsk
            (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
               inst_3
               inst_10
               inst_13
               inst_16 ts
               inst_21 tsk)
            L A)
         Bool_true ->
       @eq Bool
         (Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space Task
            inst_3
            inst_10
            inst_13 ts
            inst_21 tsk L A)
         Bool_true
```
