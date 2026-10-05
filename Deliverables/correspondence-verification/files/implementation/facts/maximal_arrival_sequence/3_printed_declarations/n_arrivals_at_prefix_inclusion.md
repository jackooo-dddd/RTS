# `n_arrivals_at_prefix_inclusion`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_prefix_inclusion`
- Certificate: `n_arrivals_at_prefix_inclusion_correspondence`

## Official Rocq

```coq
n_arrivals_at_prefix_inclusion :
forall {Task : TaskType} (ts : seq (Equality.sort Task)),
is_true (@uniq Task ts) ->
forall {H3 : MaxArrivals Task} (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall t h1 h2 : nat,
is_true (t <= h1 <= h2) ->
@nth nat 0 (@maximal_arrival_prefix Task H3 tsk h1) t = @nth nat 0 (@maximal_arrival_prefix Task H3 tsk h2) t

n_arrivals_at_prefix_inclusion is not universe polymorphic
Arguments n_arrivals_at_prefix_inclusion {Task} ts%seq_scope H_ts_uniq {H3} tsk H_tsk_in_ts
  (t h1 h2)%nat_scope _
n_arrivals_at_prefix_inclusion is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 168, characters 10-40
@n_arrivals_at_prefix_inclusion
     : forall (Task : TaskType) (ts : seq (Equality.sort Task)),
       is_true (@uniq Task ts) ->
       forall (H3 : MaxArrivals Task) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall t h1 h2 : nat,
       is_true (t <= h1 <= h2) ->
       @nth nat 0 (@maximal_arrival_prefix Task H3 tsk h1) t =
       @nth nat 0 (@maximal_arrival_prefix Task H3 tsk h2) t
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_prefix_inclusion : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] (ts : List Task),
  ts.Nodup →
    ∀ [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (t h1 h2 : ℕ),
          (decide (t ≤ h1) && decide (h1 ≤ h2)) = true →
            (Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix tsk h1).getD t 0 =
              (Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix tsk h2).getD t 0
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_n_arrivals_at_prefix_inclusion
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
       forall t h1 h2 : Nat,
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t h1) (Nat_decLe t h1))
            (Decidable_decide (LE_le_inst1 Nat instLENat h1 h2) (Nat_decLe h1 h2)))
         Bool_true ->
       @eq Nat
         (List_getD_inst1 Nat
            (Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix Task
               inst_3
               inst_9 tsk h1)
            t (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
         (List_getD_inst1 Nat
            (Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix Task
               inst_3
               inst_9 tsk h2)
            t (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
```
