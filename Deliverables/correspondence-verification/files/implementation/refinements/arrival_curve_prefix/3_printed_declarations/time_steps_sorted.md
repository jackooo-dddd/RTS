# `time_steps_sorted`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.arrival_curve_prefix.time_steps_sorted`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurvePrefix.time_steps_sorted`
- Certificate: `time_steps_sorted_correspondence`

## Official Rocq

```coq
time_steps_sorted :
forall ts : seq (Equality.sort Task),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) -> is_true (@sorted nat (@rel_of_simpl nat ltn) (get_time_steps_of_task tsk))

time_steps_sorted is not universe polymorphic
Arguments time_steps_sorted ts%_seq_scope H_valid_task_set tsk H_tsk_in_ts
time_steps_sorted is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve_prefix.time_steps_sorted
Declared in library prosa.implementation.refinements.arrival_curve_prefix, line 80, characters 8-25
time_steps_sorted
     : forall ts : seq (Equality.sort Task),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) -> is_true (@sorted nat (@rel_of_simpl nat ltn) (get_time_steps_of_task tsk))
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurvePrefix.time_steps_sorted : ∀
  (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ tsk ∈ ts,
      Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sortedBool (fun x y => decide (x < y))
          (Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task tsk) =
        true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurvePrefix_time_steps_sorted
     : forall ts : List_inst1 Prosa_Implementation_Refinements_Task_Task,
       Prosa_Implementation_Refinements_ArrivalCurve_task_set_with_valid_arrivals ts ->
       forall tsk : Prosa_Implementation_Refinements_Task_Task,
       Membership_mem_inst3 Prosa_Implementation_Refinements_Task_Task
         (List_inst1 Prosa_Implementation_Refinements_Task_Task)
         (List_instMembership_inst1 Prosa_Implementation_Refinements_Task_Task) ts tsk ->
       @eq Bool
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1
            Prosa_Behavior_Time_duration
            (fun x y : Prosa_Behavior_Time_duration =>
             Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat x y) (Nat_decLt x y))
            (Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk))
         Bool_true
```
