# `extend_horizon_size`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.extend_horizon_size`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.extend_horizon_size`
- Certificate: `extend_horizon_size_correspondence`

## Official Rocq

```coq
extend_horizon_size :
forall {Task : TaskType} (ts : seq (Equality.sort Task)),
is_true (@uniq Task ts) ->
forall {H3 : MaxArrivals Task} (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall t : nat, @size nat (@iter (seq nat) t (@extend_arrival_prefix Task H3 tsk) [::]) = t

extend_horizon_size is not universe polymorphic
Arguments extend_horizon_size {Task} ts%seq_scope H_ts_uniq {H3} tsk H_tsk_in_ts t%nat_scope
extend_horizon_size is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.extend_horizon_size
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 140, characters 10-29
@extend_horizon_size
     : forall (Task : TaskType) (ts : seq (Equality.sort Task)),
       is_true (@uniq Task ts) ->
       forall (H3 : MaxArrivals Task) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall t : nat, @size nat (@iter (seq nat) t (@extend_arrival_prefix Task H3 tsk) [::]) = t
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.extend_horizon_size : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (ts : List Task),
  ts.Nodup →
    ∀ [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (t : ℕ),
          (Nat.repeat (Prosa.Implementation.Definitions.MaximalArrivalSequence.extend_arrival_prefix tsk) t []).length =
            t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_extend_horizon_size
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (ts : List Task),
       List_Nodup Task ts ->
       forall
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall t : Nat,
       @eq Nat
         (List_length_inst1 Nat
            (Nat_repeat_inst1 (List_inst1 Nat)
               (Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix Task
                  inst_3
                  inst_9 tsk)
               t (List_nil_inst1 Nat)))
         t
```
