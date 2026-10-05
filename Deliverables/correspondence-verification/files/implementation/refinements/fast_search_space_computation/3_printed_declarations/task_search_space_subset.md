# `task_search_space_subset`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.fast_search_space_computation.task_search_space_subset`
- Lean: `Prosa.Implementation.Refinements.FastSearchSpaceComputation.task_search_space_subset`
- Certificate: `task_search_space_subset_correspondence`

## Official Rocq

```coq
task_search_space_subset :
forall (L : duration) (ts : seq (Equality.sort Task)),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
forall A : nat,
is_true (A < L) ->
is_true (task_rbf tsk A != task_rbf tsk (A + 1)) ->
is_true (A \in search_space_arrival_curve_prefix_FP tsk L)

task_search_space_subset is not universe polymorphic
Arguments task_search_space_subset L ts%_seq_scope H_valid_task_set tsk H_positive_cost 
  H_tsk_in_ts A%_nat_scope _ _
task_search_space_subset is opaque
Expands to: Constant prosa.implementation.refinements.fast_search_space_computation.task_search_space_subset
Declared in library prosa.implementation.refinements.fast_search_space_computation, line 212, characters 8-32
task_search_space_subset
     : forall (L : duration) (ts : seq (Equality.sort Task)),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       forall A : nat,
       is_true (A < L) ->
       is_true (task_rbf tsk A != task_rbf tsk (A + 1)) ->
       is_true (A \in search_space_arrival_curve_prefix_FP tsk L)
```

## Lean

```lean
Prosa.Implementation.Refinements.FastSearchSpaceComputation.task_search_space_subset : ∀
  (L : Prosa.Behavior.Time.duration) (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
      0 < Prosa.Model.Task.Concept.task_cost tsk →
        tsk ∈ ts →
          ∀ A < L,
            decide
                  (Prosa.Implementation.Refinements.ArrivalCurve.task_rbf tsk A ≠
                    Prosa.Implementation.Refinements.ArrivalCurve.task_rbf tsk (A + 1)) =
                true →
              A ∈ Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FastSearchSpaceComputation_task_search_space_subset
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
            (Ne Nat (Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk A)
               (Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk
                  (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
            (instDecidableNot
               (@eq Nat (Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk A)
                  (Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk
                     (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
               (instDecidableEqNat (Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk A)
                  (Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk
                     (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))))
         Bool_true ->
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
         (Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP
            tsk L)
         A
```
