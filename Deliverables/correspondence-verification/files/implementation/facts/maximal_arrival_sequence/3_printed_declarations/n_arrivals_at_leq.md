# `n_arrivals_at_leq`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_leq`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_leq`
- Certificate: `n_arrivals_at_leq_correspondence`

## Official Rocq

```coq
n_arrivals_at_leq :
forall {Task : TaskType} (ts : seq (Equality.sort Task)),
is_true (@uniq Task ts) ->
forall {H3 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H3) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall t Δ : nat,
is_true (Δ <= t) ->
is_true
  (@max_arrivals_at Task H3 tsk t <=
   @max_arrivals Task H3 tsk Δ.+1 - \sum_(t - Δ <= i < t) @max_arrivals_at Task H3 tsk i)

n_arrivals_at_leq is not universe polymorphic
Arguments n_arrivals_at_leq {Task} ts%seq_scope H_ts_uniq {H3} H_valid_arrival_curve 
  tsk H_tsk_in_ts (t Δ)%nat_scope _
n_arrivals_at_leq is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_leq
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 200, characters 10-27
@n_arrivals_at_leq
     : forall (Task : TaskType) (ts : seq (Equality.sort Task)),
       is_true (@uniq Task ts) ->
       forall H3 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H3) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall t Δ : nat,
       is_true (Δ <= t) ->
       is_true
         (@max_arrivals_at Task H3 tsk t <=
          @max_arrivals Task H3 tsk Δ.+1 - \sum_(t - Δ <= i < t) @max_arrivals_at Task H3 tsk i)
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_leq : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (ts : List Task),
  ts.Nodup →
    ∀ [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
      Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
        ∀ (tsk : Task),
          decide (tsk ∈ ts) = true →
            ∀ (t Δ : ℕ),
              Δ ≤ t →
                Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at tsk t ≤
                  Prosa.Model.Task.Arrival.Curves.max_arrivals tsk (Δ + 1) -
                    Prosa.Util.Sum.sumSeq (List.range' (t - Δ) (t - (t - Δ))) fun i =>
                      Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at tsk i
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_n_arrivals_at_leq
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (ts : List Task),
       List_Nodup Task ts ->
       forall
         inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_9) ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall t _UU0394_ : Nat,
       LE_le_inst1 Nat instLENat _UU0394_ t ->
       LE_le_inst1 Nat instLENat
         (Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at Task
            inst_3
            inst_9 tsk t)
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
               inst_3
               inst_9 tsk
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) _UU0394_
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
            (Prosa_Util_Sum_sumSeq_inst1 Nat
               (List_range' (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t _UU0394_)
                  (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t
                     (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t _UU0394_))
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
               (fun i : Nat =>
                Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at Task
                  inst_3
                  inst_9 tsk i)))
```
