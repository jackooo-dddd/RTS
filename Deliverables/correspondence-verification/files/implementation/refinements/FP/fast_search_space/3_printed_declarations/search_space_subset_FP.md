# `search_space_subset_FP`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.search_space_subset_FP`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_subset_FP`
- Certificate: `search_space_subset_FP_correspondence`

## Official Rocq

```coq
search_space_subset_FP :
forall (L : duration) (ts : seq (Equality.sort Task)),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
forall A : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
is_true (A \in correct_search_space tsk L) -> is_true (A \in search_space_emax_FP tsk L)

search_space_subset_FP is not universe polymorphic
Arguments search_space_subset_FP L ts%_seq_scope H_valid_arrivals tsk H_positive_cost H_tsk_in_ts A _
search_space_subset_FP is opaque
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.search_space_subset_FP
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 75, characters 8-30
search_space_subset_FP
     : forall (L : duration) (ts : seq (Equality.sort Task)),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       forall A : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
       is_true (A \in correct_search_space tsk L) -> is_true (A \in search_space_emax_FP tsk L)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_subset_FP : ∀ (L : Prosa.Behavior.Time.duration)
  (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
      0 < Prosa.Model.Task.Concept.task_cost tsk →
        tsk ∈ ts →
          ∀ A ∈ Prosa.Implementation.Refinements.FP.FastSearchSpace.correct_search_space tsk L,
            A ∈ Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_subset_FP
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
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
         (Prosa_Implementation_Refinements_FP_FastSearchSpace_correct_search_space tsk L) A ->
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
         (Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP tsk L) A
```
