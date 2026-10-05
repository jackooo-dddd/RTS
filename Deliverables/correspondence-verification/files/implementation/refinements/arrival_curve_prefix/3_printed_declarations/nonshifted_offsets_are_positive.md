# `nonshifted_offsets_are_positive`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.arrival_curve_prefix.nonshifted_offsets_are_positive`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurvePrefix.nonshifted_offsets_are_positive`
- Certificate: `nonshifted_offsets_are_positive_correspondence`

## Official Rocq

```coq
nonshifted_offsets_are_positive :
forall ts : seq (Equality.sort Task),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (0 < task_cost tsk) ->
is_true (tsk \in ts) ->
is_true (0 < (@head (nat * nat) (0, 0) (steps_of (get_arrival_curve_prefix tsk))).1) ->
forall (A : Equality.sort Datatypes_nat__canonical__eqtype_Equality) (offs : seq nat),
is_true (A \in repeat_steps_with_offset tsk offs) -> is_true (0 < A)

nonshifted_offsets_are_positive is not universe polymorphic
Arguments nonshifted_offsets_are_positive ts%_seq_scope H_valid_task_set tsk H_positive_cost 
  H_tsk_in_ts H_positive_step A offs%_seq_scope _
nonshifted_offsets_are_positive is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve_prefix.nonshifted_offsets_are_positive
Declared in library prosa.implementation.refinements.arrival_curve_prefix, line 68, characters 8-39
nonshifted_offsets_are_positive
     : forall ts : seq (Equality.sort Task),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (0 < task_cost tsk) ->
       is_true (tsk \in ts) ->
       is_true (0 < (@head (nat * nat) (0, 0) (steps_of (get_arrival_curve_prefix tsk))).1) ->
       forall (A : Equality.sort Datatypes_nat__canonical__eqtype_Equality) (offs : seq nat),
       is_true (A \in repeat_steps_with_offset tsk offs) -> is_true (0 < A)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurvePrefix.nonshifted_offsets_are_positive : ∀
  (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
      0 < Prosa.Model.Task.Concept.task_cost tsk →
        tsk ∈ ts →
          0 <
              ((Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of
                      (Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix tsk)).headD
                  (0, 0)).1 →
            ∀ (A : ℕ) (offs : List ℕ),
              A ∈ Prosa.Implementation.Refinements.ArrivalCurve.repeat_steps_with_offset tsk offs → 0 < A
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurvePrefix_nonshifted_offsets_are_positive
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
       forall (A : Nat) (offs : List_inst1 Nat),
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
         (Prosa_Implementation_Refinements_ArrivalCurve_repeat_steps_with_offset tsk offs) A ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) A
```
