# `max_arrivals_at_next_max_arrivals_eq`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.max_arrivals_at_next_max_arrivals_eq`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.max_arrivals_at_next_max_arrivals_eq`
- Certificate: `max_arrivals_at_next_max_arrivals_eq_correspondence`

## Official Rocq

```coq
max_arrivals_at_next_max_arrivals_eq :
forall {Task : TaskType} (ts : seq (Equality.sort Task)),
is_true (@uniq Task ts) ->
forall {H3 : MaxArrivals Task} (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall t : nat,
is_true (0 < t) ->
@max_arrivals_at Task H3 tsk t = @next_max_arrival Task H3 tsk (@maximal_arrival_prefix Task H3 tsk t.-1)

max_arrivals_at_next_max_arrivals_eq is not universe polymorphic
Arguments max_arrivals_at_next_max_arrivals_eq {Task} ts%seq_scope H_ts_uniq {H3} 
  tsk H_tsk_in_ts t%nat_scope _
max_arrivals_at_next_max_arrivals_eq is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.max_arrivals_at_next_max_arrivals_eq
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 184, characters 10-46
@max_arrivals_at_next_max_arrivals_eq
     : forall (Task : TaskType) (ts : seq (Equality.sort Task)),
       is_true (@uniq Task ts) ->
       forall (H3 : MaxArrivals Task) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall t : nat,
       is_true (0 < t) ->
       @max_arrivals_at Task H3 tsk t =
       @next_max_arrival Task H3 tsk (@maximal_arrival_prefix Task H3 tsk t.-1)
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.max_arrivals_at_next_max_arrivals_eq : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] (ts : List Task),
  ts.Nodup →
    ∀ [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (t : ℕ),
          0 < t →
            Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at tsk t =
              Prosa.Implementation.Definitions.MaximalArrivalSequence.next_max_arrival tsk
                (Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix tsk (t - 1))
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_max_arrivals_at_next_max_arrivals_eq
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
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) t ->
       @eq Nat
         (Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at Task
            inst_3
            inst_9 tsk t)
         (Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival Task
            inst_3
            inst_9 tsk
            (Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix Task
               inst_3
               inst_9 tsk
               (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))))
```
