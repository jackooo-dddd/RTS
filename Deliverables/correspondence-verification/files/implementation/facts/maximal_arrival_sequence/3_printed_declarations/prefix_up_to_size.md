# `prefix_up_to_size`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.prefix_up_to_size`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.prefix_up_to_size`
- Certificate: `prefix_up_to_size_correspondence`

## Official Rocq

```coq
prefix_up_to_size :
forall {Task : TaskType} (ts : seq (Equality.sort Task)),
is_true (@uniq Task ts) ->
forall {H3 : MaxArrivals Task} (tsk : Equality.sort Task),
is_true (tsk \in ts) -> forall t : nat, @size nat (@maximal_arrival_prefix Task H3 tsk t) = t.+1

prefix_up_to_size is not universe polymorphic
Arguments prefix_up_to_size {Task} ts%seq_scope H_ts_uniq {H3} tsk H_tsk_in_ts t%nat_scope
prefix_up_to_size is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.prefix_up_to_size
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 147, characters 10-27
@prefix_up_to_size
     : forall (Task : TaskType) (ts : seq (Equality.sort Task)),
       is_true (@uniq Task ts) ->
       forall (H3 : MaxArrivals Task) (tsk : Equality.sort Task),
       is_true (tsk \in ts) -> forall t : nat, @size nat (@maximal_arrival_prefix Task H3 tsk t) = t.+1
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.prefix_up_to_size : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (ts : List Task),
  ts.Nodup →
    ∀ [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (t : ℕ), (Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix tsk t).length = t + 1
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_prefix_up_to_size
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
            (Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix Task
               inst_3
               inst_9 tsk t))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
```
