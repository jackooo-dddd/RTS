# `search_space_sub`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.search_space.fifo.search_space_sub`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo.search_space_sub`
- Certificate: `search_space_sub_correspondence`

## Official Rocq

```coq
search_space_sub :
forall {SBF : sbf.SupplyBoundFunction} {Task : TaskType} {H : TaskCost Task} (ts : seq (Equality.sort Task))
  {H0 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
forall L : duration,
is_true (0 < L) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H0 tsk 1) ->
forall A : nat,
search_space.is_in_search_space L (@fifo.IBF SBF Task H ts H0 tsk) A ->
is_true (@is_in_search_space Task H ts H0 L A)

search_space_sub is not universe polymorphic
Arguments search_space_sub {SBF Task H} ts%seq_scope {H0} H_valid_arrival_curve L 
  H_L_positive tsk H_tsk_in_ts H_task_cost_pos H_arrival_curve_pos A%nat_scope _
search_space_sub is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.search_space.fifo.search_space_sub
Declared in library prosa.analysis.abstract.restricted_supply.search_space.fifo, line 80, characters 8-24
@search_space_sub
     : forall (SBF : sbf.SupplyBoundFunction) (Task : TaskType) (H : TaskCost Task)
         (ts : seq (Equality.sort Task)) (H0 : MaxArrivals Task),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       forall L : duration,
       is_true (0 < L) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H0 tsk 1) ->
       forall A : nat,
       search_space.is_in_search_space L (@fifo.IBF SBF Task H ts H0 tsk) A ->
       is_true (@is_in_search_space Task H ts H0 L A)
```

## Lean

```lean
Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo.search_space_sub : ∀
  (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction) {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] (ts : List Task)
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (L : Prosa.Behavior.Time.duration),
      0 < L →
        ∀ (tsk : Task),
          decide (tsk ∈ ts) = true →
            0 < Prosa.Model.Task.Concept.task_cost tsk →
              0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                ∀ (A : ℕ),
                  Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                      (fun A0 F =>
                        F - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F +
                          (Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts (A0 + 1) -
                            Prosa.Model.Task.Concept.task_cost tsk))
                      A →
                    Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo.is_in_search_space ts L A = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fifo_search_space_sub
     : forall (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_4 : 
          DecidableEq Task)
         (inst_7 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_4)
         (ts : List Task)
         (inst_12 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_4),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_4 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_4
            inst_12) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_4)
               (instLawfulBEq Task
                  inst_4)
               tsk ts))
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_4
            inst_7 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_4
            inst_12
            tsk (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Nat,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 F : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
               Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) F
               (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
                  inst_4
                  inst_7
                  inst_12
                  ts
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_4
                  inst_7
                  tsk)))
         A ->
       @eq Bool
         (Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fifo_is_in_search_space Task
            inst_4
            inst_7 ts
            inst_12 L
            A)
         Bool_true
```
