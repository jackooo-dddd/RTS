# `steps_lt_horizon_last_eq_horizon`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.fast_search_space_computation.steps_lt_horizon_last_eq_horizon`
- Lean: `Prosa.Implementation.Refinements.FastSearchSpaceComputation.steps_lt_horizon_last_eq_horizon`
- Certificate: `steps_lt_horizon_last_eq_horizon_correspondence`

## Official Rocq

```coq
steps_lt_horizon_last_eq_horizon :
forall ts : seq (Equality.sort Task),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
(forall s : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
 is_true (s \in get_time_steps_of_task tsk) -> is_true (s < get_horizon_of_task tsk)) \/
last0 (get_time_steps_of_task tsk) = get_horizon_of_task tsk

steps_lt_horizon_last_eq_horizon is not universe polymorphic
Arguments steps_lt_horizon_last_eq_horizon ts%_seq_scope H_valid_task_set tsk H_positive_cost H_tsk_in_ts
steps_lt_horizon_last_eq_horizon is opaque
Expands to: Constant
            prosa.implementation.refinements.fast_search_space_computation.steps_lt_horizon_last_eq_horizon
Declared in library prosa.implementation.refinements.fast_search_space_computation, line 39, characters 8-40
steps_lt_horizon_last_eq_horizon
     : forall ts : seq (Equality.sort Task),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       (forall s : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
        is_true (s \in get_time_steps_of_task tsk) -> is_true (s < get_horizon_of_task tsk)) \/
       last0 (get_time_steps_of_task tsk) = get_horizon_of_task tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.FastSearchSpaceComputation.steps_lt_horizon_last_eq_horizon : ∀
  (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
      0 < Prosa.Model.Task.Concept.task_cost tsk →
        tsk ∈ ts →
          (∀ s ∈ Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task tsk,
              s < Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk) ∨
            Prosa.Util.List.last0 (Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task tsk) =
              Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FastSearchSpaceComputation_steps_lt_horizon_last_eq_horizon
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
       Or
         (forall s : Nat,
          Membership_mem_inst3 Nat (List_inst1 Prosa_Behavior_Time_duration)
            (List_instMembership_inst1 Prosa_Behavior_Time_duration)
            (Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk) s ->
          LT_lt_inst1 Nat instLTNat s (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk))
         (@eq Nat
            (Prosa_Util_List_last0 (Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk))
            (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk))
```
