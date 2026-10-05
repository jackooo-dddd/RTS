# `steps_are_positive_if_first_step_is_positive`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.arrival_curve_prefix.steps_are_positive_if_first_step_is_positive`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurvePrefix.steps_are_positive_if_first_step_is_positive`
- Certificate: `steps_are_positive_if_first_step_is_positive_correspondence`

## Official Rocq

```coq
steps_are_positive_if_first_step_is_positive :
forall ts : seq (Equality.sort Task),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
is_true (0 < (@head (nat * nat) (0, 0) (steps_of (get_arrival_curve_prefix tsk))).1) ->
forall st : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
is_true (st \in get_time_steps_of_task tsk) -> is_true (0 < st)

steps_are_positive_if_first_step_is_positive is not universe polymorphic
Arguments steps_are_positive_if_first_step_is_positive ts%_seq_scope H_valid_task_set 
  tsk H_positive_cost H_tsk_in_ts H_positive_step st _
steps_are_positive_if_first_step_is_positive is opaque
Expands to: Constant
            prosa.implementation.refinements.arrival_curve_prefix.steps_are_positive_if_first_step_is_positive
Declared in library prosa.implementation.refinements.arrival_curve_prefix, line 40, characters 8-52
steps_are_positive_if_first_step_is_positive
     : forall ts : seq (Equality.sort Task),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       is_true (0 < (@head (nat * nat) (0, 0) (steps_of (get_arrival_curve_prefix tsk))).1) ->
       forall st : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
       is_true (st \in get_time_steps_of_task tsk) -> is_true (0 < st)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurvePrefix.steps_are_positive_if_first_step_is_positive : ∀
  (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
      0 < Prosa.Model.Task.Concept.task_cost tsk →
        tsk ∈ ts →
          0 <
              ((Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of
                      (Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix tsk)).headD
                  (0, 0)).1 →
            ∀ st ∈ Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task tsk, 0 < st
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurvePrefix_steps_are_positive_if_first_step_is_positive
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
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat
            (List_headD_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)
               (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of
                  (Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix tsk))
               (Prod_mk_inst3 Prosa_Behavior_Time_duration Nat
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
                  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))))) ->
       forall st : Nat,
       Membership_mem_inst3 Nat (List_inst1 Prosa_Behavior_Time_duration)
         (List_instMembership_inst1 Prosa_Behavior_Time_duration)
         (Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk) st ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) st
```
