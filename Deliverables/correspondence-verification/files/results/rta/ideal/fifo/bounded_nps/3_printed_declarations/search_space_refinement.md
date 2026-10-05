# `search_space_refinement`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fifo.bounded_nps.search_space_refinement`
- Lean: `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.search_space_refinement`
- Certificate: `search_space_refinement_correspondence`

## Official Rocq

```coq
search_space_refinement :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall L : duration,
is_true (0 < L) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H0 tsk 1) ->
forall A : nat,
       (fun A1 : duration =>
        fun=> \sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A1 + 1) - @task_cost Task H tsk)]
  A ->
is_true (@is_in_concrete_search_space Task H H0 ts L A)

search_space_refinement is not universe polymorphic
Arguments search_space_refinement {Task H H0} ts%seq_scope H_valid_arrival_curve 
  tsk H_tsk_in_ts L H_L_positive H_task_cost_pos H_arrival_curve_pos A%nat_scope 
  H_in_abstract
search_space_refinement is opaque
Expands to: Constant prosa.results.rta.ideal.fifo.bounded_nps.search_space_refinement
Declared in library prosa.results.rta.ideal.fifo.bounded_nps, line 348, characters 10-33
@search_space_refinement
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall L : duration,
       is_true (0 < L) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H0 tsk 1) ->
       forall A : nat,
       is_in_search_space L
         (fun A0 : duration =>
          fun=> \sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A0 + 1) -
                @task_cost Task H tsk)
         A ->
       is_true (@is_in_concrete_search_space Task H H0 ts L A)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fifo.BoundedNps.search_space_refinement : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (L : Prosa.Behavior.Time.duration),
          0 < L →
            0 < Prosa.Model.Task.Concept.task_cost tsk →
              0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                ∀ (A : ℕ),
                  Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                      (fun A0 x =>
                        (Prosa.Util.Sum.sumSeq ts fun tsko =>
                            Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko (A0 + 1)) -
                          Prosa.Model.Task.Concept.task_cost tsk)
                      A →
                    Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space ts L A = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_search_space_refinement
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13) ->
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
            inst_10 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Nat,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 _ : Prosa_Behavior_Time_duration =>
          HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Util_Sum_sumSeq Task ts
               (fun tsko : Task =>
                Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_10
                  inst_13 tsko
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_10 tsk))
         A ->
       @eq Bool
         (Prosa_Results_Rta_Ideal_Fifo_BoundedNps_is_in_concrete_search_space Task
            inst_3
            inst_10
            inst_13 ts L A)
         Bool_true
```
