# `split_hep_rbf_weaken`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.split_hep_rbf_weaken`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.split_hep_rbf_weaken`
- Certificate: `split_hep_rbf_weaken_correspondence`

## Official Rocq

```coq
split_hep_rbf_weaken :
forall {Task : TaskType} {H : TaskCost Task} {H2 : MaxArrivals Task} {FP : FP_policy Task}
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
@reflexive_task_priorities Task FP ->
forall Δ : duration,
is_true (tsk \in ts) ->
is_true
  (@total_ohep_request_bound_function_FP Task H H2 ts FP tsk Δ + @task_request_bound_function Task H H2 tsk Δ <=
   @total_hep_request_bound_function_FP Task H H2 ts FP tsk Δ)

split_hep_rbf_weaken is not universe polymorphic
Arguments split_hep_rbf_weaken {Task H H2 FP} ts%seq_scope tsk H_priority_is_reflexive Δ _
split_hep_rbf_weaken is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.split_hep_rbf_weaken
Declared in library prosa.analysis.facts.model.rbf, line 570, characters 8-28
@split_hep_rbf_weaken
     : forall (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (FP : FP_policy Task)
         (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       @reflexive_task_priorities Task FP ->
       forall Δ : duration,
       is_true (tsk \in ts) ->
       is_true
         (@total_ohep_request_bound_function_FP Task H H2 ts FP tsk Δ +
          @task_request_bound_function Task H H2 tsk Δ <=
          @total_hep_request_bound_function_FP Task H H2 ts FP tsk Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.split_hep_rbf_weaken : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (FP : Prosa.Model.Priority.Definitions.FP_policy Task)
  (ts : List Task) (tsk : Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    ∀ (Δ : Prosa.Behavior.Time.duration),
      decide (tsk ∈ ts) = true →
        Prosa.Analysis.Definitions.RequestBoundFunction.total_ohep_request_bound_function_FP ts tsk Δ +
            Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk Δ ≤
          Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_split_hep_rbf_weaken
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (ts : List Task) (tsk : Task),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task inst_3)
               (instLawfulBEq Task inst_3) tsk ts))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP Task
               inst_3
               inst_6
               inst_9 ts FP tsk _UU0394_)
            (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
               inst_3
               inst_6
               inst_9 tsk _UU0394_))
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
            inst_3
            inst_6
            inst_9 ts FP tsk _UU0394_)
```
