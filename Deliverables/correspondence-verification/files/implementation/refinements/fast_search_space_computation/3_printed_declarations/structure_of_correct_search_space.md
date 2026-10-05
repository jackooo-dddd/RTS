# `structure_of_correct_search_space`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.fast_search_space_computation.structure_of_correct_search_space`
- Lean: `Prosa.Implementation.Refinements.FastSearchSpaceComputation.structure_of_correct_search_space`
- Certificate: `structure_of_correct_search_space_correspondence`

## Official Rocq

```coq
structure_of_correct_search_space :
forall (L : duration) (ts : seq (Equality.sort Task)),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
forall A : nat,
is_true (A < L) ->
is_true (task_rbf tsk A != task_rbf tsk (A + 1)) ->
(exists (i : nat) (t : Equality.sort Datatypes_nat__canonical__eqtype_Equality),
   is_true (i < (L %/ get_horizon_of_task tsk).+1) /\
   is_true (t \in get_time_steps_of_task tsk) /\ A + 1 = i * get_horizon_of_task tsk + t) \/
exists i : nat, is_true (i < (L %/ get_horizon_of_task tsk).+1) /\ A + 1 = i * get_horizon_of_task tsk

structure_of_correct_search_space is not universe polymorphic
Arguments structure_of_correct_search_space L ts%_seq_scope H_valid_task_set tsk 
  H_positive_cost H_tsk_in_ts A%_nat_scope _ _
structure_of_correct_search_space is opaque
Expands to: Constant
            prosa.implementation.refinements.fast_search_space_computation.structure_of_correct_search_space
Declared in library prosa.implementation.refinements.fast_search_space_computation, line 69, characters 8-41
structure_of_correct_search_space
     : forall (L : duration) (ts : seq (Equality.sort Task)),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       forall A : nat,
       is_true (A < L) ->
       is_true (task_rbf tsk A != task_rbf tsk (A + 1)) ->
       (exists (i : nat) (t : Equality.sort Datatypes_nat__canonical__eqtype_Equality),
          is_true (i < (L %/ get_horizon_of_task tsk).+1) /\
          is_true (t \in get_time_steps_of_task tsk) /\ A + 1 = i * get_horizon_of_task tsk + t) \/
       exists i : nat, is_true (i < (L %/ get_horizon_of_task tsk).+1) /\ A + 1 = i * get_horizon_of_task tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.FastSearchSpaceComputation.structure_of_correct_search_space : ∀
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
              (∃ i t,
                  i < L / Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk + 1 ∧
                    t ∈ Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task tsk ∧
                      A + 1 = i * Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk + t) ∨
                ∃ i < L / Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk + 1,
                  A + 1 = i * Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FastSearchSpaceComputation_structure_of_correct_search_space
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
       Or
         (Exists Nat
            (fun i : Nat =>
             Exists Nat
               (fun t : Nat =>
                And
                  (LT_lt_inst1 Nat instLTNat i
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                        (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                        (HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                           Prosa_Behavior_Time_duration
                           (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv) L
                           (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk))
                        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                  (And
                     (Membership_mem_inst3 Nat (List_inst1 Prosa_Behavior_Time_duration)
                        (List_instMembership_inst1 Prosa_Behavior_Time_duration)
                        (Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk) t)
                     (@eq Nat
                        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A
                           (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                           (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat
                              (instHMul_inst1 Nat instMulNat) i
                              (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk))
                           t))))))
         (Exists Nat
            (fun i : Nat =>
             And
               (LT_lt_inst1 Nat instLTNat i
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                     (HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_duration
                        (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv) L
                        (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk))
                     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
               (@eq Nat
                  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A
                     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) i
                     (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk)))))
```
