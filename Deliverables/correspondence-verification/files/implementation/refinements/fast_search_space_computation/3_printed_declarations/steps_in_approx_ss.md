# `steps_in_approx_ss`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.fast_search_space_computation.steps_in_approx_ss`
- Lean: `Prosa.Implementation.Refinements.FastSearchSpaceComputation.steps_in_approx_ss`
- Certificate: `steps_in_approx_ss_correspondence`

## Official Rocq

```coq
steps_in_approx_ss :
forall (L : duration) (ts : seq (Equality.sort Task)),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
forall (i : nat) (t : Equality.sort Datatypes_nat__canonical__eqtype_Equality) (A : nat),
is_true (i < (L %/ get_horizon_of_task tsk).+1) ->
is_true (t \in get_time_steps_of_task tsk) ->
A + 1 = i * get_horizon_of_task tsk + t -> is_true (A \in search_space_arrival_curve_prefix_FP tsk L)

steps_in_approx_ss is not universe polymorphic
Arguments steps_in_approx_ss L ts%_seq_scope H_valid_task_set tsk H_positive_cost 
  H_tsk_in_ts i%_nat_scope t A%_nat_scope _ _ _
steps_in_approx_ss is opaque
Expands to: Constant prosa.implementation.refinements.fast_search_space_computation.steps_in_approx_ss
Declared in library prosa.implementation.refinements.fast_search_space_computation, line 147, characters 8-26
steps_in_approx_ss
     : forall (L : duration) (ts : seq (Equality.sort Task)),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       forall (i : nat) (t : Equality.sort Datatypes_nat__canonical__eqtype_Equality) (A : nat),
       is_true (i < (L %/ get_horizon_of_task tsk).+1) ->
       is_true (t \in get_time_steps_of_task tsk) ->
       A + 1 = i * get_horizon_of_task tsk + t -> is_true (A \in search_space_arrival_curve_prefix_FP tsk L)
```

## Lean

```lean
Prosa.Implementation.Refinements.FastSearchSpaceComputation.steps_in_approx_ss : ∀ (L : Prosa.Behavior.Time.duration)
  (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
      0 < Prosa.Model.Task.Concept.task_cost tsk →
        tsk ∈ ts →
          ∀ (i t A : ℕ),
            i < L / Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk + 1 →
              t ∈ Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task tsk →
                A + 1 = i * Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk + t →
                  A ∈
                    Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP tsk
                      L
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FastSearchSpaceComputation_steps_in_approx_ss
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
       forall i t A : Nat,
       LT_lt_inst1 Nat instLTNat i
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv) L
               (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk))
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       Membership_mem_inst3 Nat (List_inst1 Prosa_Behavior_Time_duration)
         (List_instMembership_inst1 Prosa_Behavior_Time_duration)
         (Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk) t ->
       @eq Nat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) i
               (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk))
            t) ->
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
         (Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP
            tsk L)
         A
```
