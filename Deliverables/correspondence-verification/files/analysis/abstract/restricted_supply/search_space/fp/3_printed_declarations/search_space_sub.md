# `search_space_sub`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.search_space.fp.search_space_sub`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp.search_space_sub`
- Certificate: `search_space_sub_correspondence`

## Official Rocq

```coq
search_space_sub :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskMaxNonpreemptiveSegment Task} 
  {FP : FP_policy Task} (ts : seq (Equality.sort Task)) {H1 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H1) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall L : duration,
is_true (0 < L) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H1 tsk 1) ->
forall A : nat,
search_space.is_in_search_space L
  (fun A0 F : duration =>
   @task_request_bound_function Task H H1 tsk (A0 + 1) - @task_cost Task H tsk +
   (@blocking_bound Task H0 FP ts tsk + @total_ohep_request_bound_function_FP Task H H1 ts FP tsk F))
  A ->
is_true (@is_in_search_space Task H H1 tsk L A)

search_space_sub is not universe polymorphic
Arguments search_space_sub {Task H H0 FP} ts%seq_scope {H1} H_valid_arrival_curve 
  tsk H_tsk_in_ts L H_L_positive H_task_cost_pos H_arrival_curve_pos A%nat_scope 
  _
search_space_sub is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.search_space.fp.search_space_sub
Declared in library prosa.analysis.abstract.restricted_supply.search_space.fp, line 80, characters 8-24
@search_space_sub
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskMaxNonpreemptiveSegment Task)
         (FP : FP_policy Task) (ts : seq (Equality.sort Task)) (H1 : MaxArrivals Task),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H1) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall L : duration,
       is_true (0 < L) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H1 tsk 1) ->
       forall A : nat,
       search_space.is_in_search_space L
         (fun A0 F : duration =>
          @task_request_bound_function Task H H1 tsk (A0 + 1) - @task_cost Task H tsk +
          (@blocking_bound Task H0 FP ts tsk + @total_ohep_request_bound_function_FP Task H H1 ts FP tsk F))
         A ->
       is_true (@is_in_search_space Task H H1 tsk L A)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp.search_space_sub : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (ts : List Task)
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (L : Prosa.Behavior.Time.duration),
          0 < L →
            0 < Prosa.Model.Task.Concept.task_cost tsk →
              0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                ∀ (A : ℕ),
                  Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                      (fun A0 F =>
                        Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A0 + 1) -
                            Prosa.Model.Task.Concept.task_cost tsk +
                          (Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk +
                            Prosa.Analysis.Definitions.RequestBoundFunction.total_ohep_request_bound_function_FP ts tsk
                              F))
                      A →
                    Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp.is_in_search_space tsk L A = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fp_search_space_sub
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (ts : List Task)
         (inst_16 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_16) ->
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
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_6 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_16 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Nat,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 F : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_6
                  inst_16
                  tsk
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_3
                  inst_6
                  tsk))
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
               (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
                  inst_3
                  inst_9
                  FP ts tsk)
               (Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP Task
                  inst_3
                  inst_6
                  inst_16
                  ts FP tsk F)))
         A ->
       @eq Bool
         (Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fp_is_in_search_space Task
            inst_3
            inst_6
            inst_16 tsk
            L A)
         Bool_true
```
