# `multiple_of_horizon_in_approx_ss`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.fast_search_space_computation.multiple_of_horizon_in_approx_ss`
- Lean: `Prosa.Implementation.Refinements.FastSearchSpaceComputation.multiple_of_horizon_in_approx_ss`
- Certificate: `multiple_of_horizon_in_approx_ss_correspondence`

## Official Rocq

```coq
multiple_of_horizon_in_approx_ss :
forall (L : duration) (ts : seq (Equality.sort Task)),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
forall A : nat,
is_true (A < L) ->
is_true (get_horizon_of_task tsk %| A) -> is_true (A \in search_space_arrival_curve_prefix_FP tsk L)

multiple_of_horizon_in_approx_ss is not universe polymorphic
Arguments multiple_of_horizon_in_approx_ss L ts%_seq_scope H_valid_task_set tsk H_positive_cost 
  H_tsk_in_ts A%_nat_scope _ _
multiple_of_horizon_in_approx_ss is opaque
Expands to: Constant
            prosa.implementation.refinements.fast_search_space_computation.multiple_of_horizon_in_approx_ss
Declared in library prosa.implementation.refinements.fast_search_space_computation, line 119, characters 8-40
multiple_of_horizon_in_approx_ss
     : forall (L : duration) (ts : seq (Equality.sort Task)),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       forall A : nat,
       is_true (A < L) ->
       is_true (get_horizon_of_task tsk %| A) -> is_true (A \in search_space_arrival_curve_prefix_FP tsk L)
```

## Lean

```lean
Prosa.Implementation.Refinements.FastSearchSpaceComputation.multiple_of_horizon_in_approx_ss : ∀
  (L : Prosa.Behavior.Time.duration) (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
      0 < Prosa.Model.Task.Concept.task_cost tsk →
        tsk ∈ ts →
          ∀ A < L,
            decide (Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk ∣ A) = true →
              A ∈ Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FastSearchSpaceComputation_multiple_of_horizon_in_approx_ss
     : forall (L : Prosa_Behavior_Time_duration) (ts : List_inst1 Prosa_Implementation_Refinements_Task_Task),
       Prosa_Implementation_Refinements_ArrivalCurve_task_set_with_valid_arrivals ts ->
       forall tsk : Prosa_Implementation_Refinements_Task_Task,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost_inst1 Prosa_Implementation_Refinements_Task_Task
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
            Prosa_Implementation_Definitions_Task_TaskCost tsk) ->
       Membership_mem_inst3 Prosa_Implementation_Refinements_Task_Task
         (List_inst1 Prosa_Implementation_Refinements_Task_Task)
         (List_instMembership_inst1 Prosa_Implementation_Refinements_Task_Task) ts tsk ->
       forall A : Nat,
       LT_lt_inst1 Nat instLTNat A L ->
       @eq Bool
         (Decidable_decide
            (Dvd_dvd_inst1 Prosa_Behavior_Time_duration Nat_instDvd
               (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk) A)
            (Nat_decidable_dvd (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk) A))
         Bool_true ->
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
         (Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP
            tsk L)
         A
```
