# `has_valid_arrival_curve_prefix_tsk`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.arrival_curve_prefix.has_valid_arrival_curve_prefix_tsk`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurvePrefix.has_valid_arrival_curve_prefix_tsk`
- Certificate: `has_valid_arrival_curve_prefix_tsk_correspondence`

## Official Rocq

```coq
has_valid_arrival_curve_prefix_tsk :
forall ts : seq (Equality.sort Task),
task_set_with_valid_arrivals ts ->
forall tsk : Equality.sort Task, is_true (tsk \in ts) -> has_valid_arrival_curve_prefix tsk

has_valid_arrival_curve_prefix_tsk is not universe polymorphic
Arguments has_valid_arrival_curve_prefix_tsk ts%_seq_scope H_valid_task_set tsk H_tsk_in_ts
has_valid_arrival_curve_prefix_tsk is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve_prefix.has_valid_arrival_curve_prefix_tsk
Declared in library prosa.implementation.refinements.arrival_curve_prefix, line 20, characters 8-42
has_valid_arrival_curve_prefix_tsk
     : forall ts : seq (Equality.sort Task),
       task_set_with_valid_arrivals ts ->
       forall tsk : Equality.sort Task, is_true (tsk \in ts) -> has_valid_arrival_curve_prefix tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurvePrefix.has_valid_arrival_curve_prefix_tsk : ∀
  (ts : List Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals ts →
    ∀ tsk ∈ ts, Prosa.Implementation.Refinements.ArrivalCurve.has_valid_arrival_curve_prefix tsk
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurvePrefix_has_valid_arrival_curve_prefix_tsk
     : forall ts : List_inst1 Prosa_Implementation_Refinements_Task_Task,
       Prosa_Implementation_Refinements_ArrivalCurve_task_set_with_valid_arrivals ts ->
       forall tsk : Prosa_Implementation_Refinements_Task_Task,
       Membership_mem_inst3 Prosa_Implementation_Refinements_Task_Task
         (List_inst1 Prosa_Implementation_Refinements_Task_Task)
         (List_instMembership_inst1 Prosa_Implementation_Refinements_Task_Task) ts tsk ->
       Prosa_Implementation_Refinements_ArrivalCurve_has_valid_arrival_curve_prefix tsk
```
