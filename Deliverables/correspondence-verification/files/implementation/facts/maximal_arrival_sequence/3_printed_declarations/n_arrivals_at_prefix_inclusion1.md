# `n_arrivals_at_prefix_inclusion1`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion1`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_prefix_inclusion1`
- Certificate: `n_arrivals_at_prefix_inclusion1_correspondence`

## Official Rocq

```coq
n_arrivals_at_prefix_inclusion1 :
forall {Task : TaskType} (ts : seq (Equality.sort Task)),
is_true (@uniq Task ts) ->
forall {H3 : MaxArrivals Task} (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall t h : nat,
is_true (t <= h) ->
@nth nat 0 (@maximal_arrival_prefix Task H3 tsk h) t =
@nth nat 0 (@maximal_arrival_prefix Task H3 tsk h.+1) t

n_arrivals_at_prefix_inclusion1 is not universe polymorphic
Arguments n_arrivals_at_prefix_inclusion1 {Task} ts%seq_scope H_ts_uniq {H3} tsk 
  H_tsk_in_ts (t h)%nat_scope _
n_arrivals_at_prefix_inclusion1 is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion1
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 156, characters 10-41
@n_arrivals_at_prefix_inclusion1
     : forall (Task : TaskType) (ts : seq (Equality.sort Task)),
       is_true (@uniq Task ts) ->
       forall (H3 : MaxArrivals Task) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall t h : nat,
       is_true (t <= h) ->
       @nth nat 0 (@maximal_arrival_prefix Task H3 tsk h) t =
       @nth nat 0 (@maximal_arrival_prefix Task H3 tsk h.+1) t
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_prefix_inclusion1 : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] (ts : List Task),
  ts.Nodup →
    ∀ [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (t h : ℕ),
          t ≤ h →
            (Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix tsk h).getD t 0 =
              (Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix tsk (h + 1)).getD t 0
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_n_arrivals_at_prefix_inclusion1
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
       forall t h : Nat,
       LE_le_inst1 Nat instLENat t h ->
       @eq Nat
         (List_getD_inst1 Nat
            (Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix Task
               inst_3
               inst_9 tsk h)
            t (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
         (List_getD_inst1 Nat
            (Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix Task
               inst_3
               inst_9 tsk
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) h
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
            t (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
```
