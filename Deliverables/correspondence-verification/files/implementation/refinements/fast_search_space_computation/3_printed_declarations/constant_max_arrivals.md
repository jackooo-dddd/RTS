# `constant_max_arrivals`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.fast_search_space_computation.constant_max_arrivals`
- Lean: `Prosa.Implementation.Refinements.FastSearchSpaceComputation.constant_max_arrivals`
- Certificate: `constant_max_arrivals_correspondence`

## Official Rocq

```coq
constant_max_arrivals :
forall ts : seq (Equality.sort Task),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
forall A : nat,
(forall s : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
 is_true (s \in get_time_steps_of_task tsk) -> is_true (s < get_horizon_of_task tsk)) ->
is_true (get_horizon_of_task tsk %| A + 1) ->
@max_arrivals Task ConcreteMaxArrivals tsk A = @max_arrivals Task ConcreteMaxArrivals tsk (A + 1)

constant_max_arrivals is not universe polymorphic
Arguments constant_max_arrivals ts%_seq_scope H_valid_task_set tsk H_positive_cost 
  H_tsk_in_ts A%_nat_scope _%_function_scope _
constant_max_arrivals is opaque
Expands to: Constant prosa.implementation.refinements.fast_search_space_computation.constant_max_arrivals
Declared in library prosa.implementation.refinements.fast_search_space_computation, line 167, characters 8-29
constant_max_arrivals
     : forall ts : seq (Equality.sort Task),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       forall A : nat,
       (forall s : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
        is_true (s \in get_time_steps_of_task tsk) -> is_true (s < get_horizon_of_task tsk)) ->
       is_true (get_horizon_of_task tsk %| A + 1) ->
       @max_arrivals Task ConcreteMaxArrivals tsk A = @max_arrivals Task ConcreteMaxArrivals tsk (A + 1)
```

## Lean

```lean
Prosa.Implementation.Refinements.FastSearchSpaceComputation.constant_max_arrivals : ∀
  (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
      0 < Prosa.Model.Task.Concept.task_cost tsk →
        tsk ∈ ts →
          ∀ (A : ℕ),
            (∀ s ∈ Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task tsk,
                s < Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk) →
              decide (Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk ∣ A + 1) = true →
                Prosa.Model.Task.Arrival.Curves.max_arrivals tsk A =
                  Prosa.Model.Task.Arrival.Curves.max_arrivals tsk (A + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FastSearchSpaceComputation_constant_max_arrivals
     : forall ts : List_inst1 Prosa_Implementation_Refinements_Task_Task,
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
       (forall s : Nat,
        Membership_mem_inst3 Nat (List_inst1 Prosa_Behavior_Time_duration)
          (List_instMembership_inst1 Prosa_Behavior_Time_duration)
          (Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk) s ->
        LT_lt_inst1 Nat instLTNat s (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk)) ->
       @eq Bool
         (Decidable_decide
            (Dvd_dvd_inst1 Prosa_Behavior_Time_duration Nat_instDvd
               (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk)
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
            (Nat_decidable_dvd (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk)
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
         Bool_true ->
       @eq Nat
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals_inst1
            Prosa_Implementation_Refinements_Task_Task
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
            Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals tsk A)
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals_inst1
            Prosa_Implementation_Refinements_Task_Task
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
            Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals tsk
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
```
