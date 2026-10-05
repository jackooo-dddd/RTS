# `task_with_equal_deadline_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.edf.bounded_nps.task_with_equal_deadline_exists`
- Lean: `Prosa.Results.Rta.Ideal.Edf.BoundedNps.task_with_equal_deadline_exists`
- Certificate: `task_with_equal_deadline_exists_correspondence`

## Official Rocq

```coq
task_with_equal_deadline_exists :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H2 : TaskMaxNonpreemptiveSegment Task}
  (ts : seq (Equality.sort Task)) {H5 : MaxArrivals Task} (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {A : duration},
is_true (priority_inversion_changes_at (@blocking_bound Task H H0 H2 ts H5 tsk) A) ->
exists tsk_o : Equality.sort Task,
  is_true
    ((tsk_o \in ts) && @blocking_relevant Task H H5 tsk_o && (tsk_o != tsk) &&
     ([eta @task_deadline Task H0] tsk_o == [eta @task_deadline Task H0] tsk + A))

task_with_equal_deadline_exists is not universe polymorphic
Arguments task_with_equal_deadline_exists {Task H H0 H2} ts%seq_scope {H5} tsk H_tsk_in_ts {A} _
task_with_equal_deadline_exists is opaque
Expands to: Constant prosa.results.rta.ideal.edf.bounded_nps.task_with_equal_deadline_exists
Declared in library prosa.results.rta.ideal.edf.bounded_nps, line 150, characters 8-39
@task_with_equal_deadline_exists
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task)
         (H2 : TaskMaxNonpreemptiveSegment Task) (ts : seq (Equality.sort Task)) 
         (H5 : MaxArrivals Task) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall A : duration,
       is_true (priority_inversion_changes_at (@blocking_bound Task H H0 H2 ts H5 tsk) A) ->
       exists tsk_o : Equality.sort Task,
         is_true
           ((tsk_o \in ts) && @blocking_relevant Task H H5 tsk_o && (tsk_o != tsk) &&
            (@task_deadline Task H0 tsk_o == @task_deadline Task H0 tsk + A))
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.BoundedNps.task_with_equal_deadline_exists : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] (ts : List Task)
  [inst_4 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ (A : Prosa.Behavior.Time.duration),
      Prosa.Results.Rta.Ideal.Edf.BoundedPi.priority_inversion_changes_at
            (Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk) A =
          true →
        ∃ tsk_o,
          (decide (tsk_o ∈ ts) && Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_relevant tsk_o &&
                decide (tsk_o ≠ tsk) &&
              decide (Prosa.Model.Task.Concept.task_deadline tsk_o = Prosa.Model.Task.Concept.task_deadline tsk + A)) =
            true
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedNps_task_with_equal_deadline_exists
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
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall A : Prosa_Behavior_Time_duration,
       @eq Bool
         (Prosa_Results_Rta_Ideal_Edf_BoundedPi_priority_inversion_changes_at
            (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
               inst_3
               inst_10
               inst_13
               inst_16 ts
               inst_21 tsk)
            A)
         Bool_true ->
       Exists Task
         (fun tsk_o : Task =>
          Bool_and
            (Bool_and
               (Bool_and
                  (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk_o)
                     (List_instDecidableMemOfLawfulBEq Task
                        (instBEqOfDecidableEq Task
                           inst_3)
                        (instLawfulBEq Task
                           inst_3)
                        tsk_o ts))
                  (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant Task
                     inst_3
                     inst_10
                     inst_21 tsk_o))
               (Decidable_decide (Ne Task tsk_o tsk)
                  (instDecidableNot (@eq Task tsk_o tsk)
                     (inst_3 tsk_o tsk))))
            (Decidable_decide
               (@eq Prosa_Behavior_Time_duration
                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                     inst_3
                     inst_13 tsk_o)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                        inst_3
                        inst_13 tsk)
                     A))
               (instDecidableEqNat
                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                     inst_3
                     inst_13 tsk_o)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                        inst_3
                        inst_13 tsk)
                     A))) =
          Bool_true)
```
