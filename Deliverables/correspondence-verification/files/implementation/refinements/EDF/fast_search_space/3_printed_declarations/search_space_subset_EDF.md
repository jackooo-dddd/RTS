# `search_space_subset_EDF`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.search_space_subset_EDF`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_subset_EDF`
- Certificate: `search_space_subset_EDF_correspondence`

## Official Rocq

```coq
search_space_subset_EDF :
forall (L : duration) (ts : seq (Equality.sort Task)),
task_set_with_valid_arrivals ts ->
(forall tsk : Equality.sort Task, is_true (tsk \in ts) -> is_true (0 < task_cost tsk)) ->
(forall tsk : Equality.sort Task,
 is_true (tsk \in ts) -> is_true (0 < (@head (nat * nat) (0, 0) (steps_of (get_arrival_curve_prefix tsk))).1)) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall A : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
is_true (A \in correct_search_space ts tsk L) -> is_true (A \in search_space_emax_EDF ts tsk L)

search_space_subset_EDF is not universe polymorphic
Arguments search_space_subset_EDF L ts%_seq_scope H_valid_task_set
  (H_all_tsk_positive_cost H_all_tsk_positive_step)%_function_scope tsk H_tsk_in_ts 
  A _
search_space_subset_EDF is opaque
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.search_space_subset_EDF
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 121, characters 8-31
search_space_subset_EDF
     : forall (L : duration) (ts : seq (Equality.sort Task)),
       task_set_with_valid_arrivals ts ->
       (forall tsk : Equality.sort Task, is_true (tsk \in ts) -> is_true (0 < task_cost tsk)) ->
       (forall tsk : Equality.sort Task,
        is_true (tsk \in ts) ->
        is_true (0 < (@head (nat * nat) (0, 0) (steps_of (get_arrival_curve_prefix tsk))).1)) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall A : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
       is_true (A \in correct_search_space ts tsk L) -> is_true (A \in search_space_emax_EDF ts tsk L)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_subset_EDF : ∀ (L : Prosa.Behavior.Time.duration)
  (ts : List Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    (∀ tsk ∈ ts, 0 < Prosa.Model.Task.Concept.task_cost tsk) →
      (∀ tsk ∈ ts,
          0 <
            ((Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of
                    (Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix tsk)).headD
                (0, 0)).1) →
        ∀ tsk ∈ ts,
          ∀ A ∈ Prosa.Implementation.Refinements.EDF.FastSearchSpace.correct_search_space ts tsk L,
            A ∈ Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_EDF ts tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_subset_EDF
     : forall (L : Prosa_Behavior_Time_duration)
         (ts : List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task),
       Prosa_Implementation_Refinements_ArrivalCurve_task_set_with_valid_arrivals ts ->
       (forall tsk : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task,
        Membership_mem_inst3 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
          (List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task)
          (List_instMembership_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) ts tsk ->
        LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
          (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
          (Prosa_Model_Task_Concept_TaskCost_task_cost_inst1
             Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
             Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
             Prosa_Implementation_Definitions_Task_TaskCost tsk)) ->
       (forall tsk : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task,
        Membership_mem_inst3 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
          (List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task)
          (List_instMembership_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) ts tsk ->
        LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
          (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
          (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat
             (List_headD_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)
                (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of
                   (Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix tsk))
                (Prod_mk_inst3 Prosa_Behavior_Time_duration Nat
                   (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
                   (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))))) ->
       forall tsk : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task,
       Membership_mem_inst3 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
         (List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task)
         (List_instMembership_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) ts tsk ->
       forall A : Nat,
       Membership_mem_inst3 Nat (List_inst1 Prosa_Behavior_Time_duration)
         (List_instMembership_inst1 Prosa_Behavior_Time_duration)
         (Prosa_Implementation_Refinements_EDF_FastSearchSpace_correct_search_space ts tsk L) A ->
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
         (Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_EDF ts tsk L) A
```
