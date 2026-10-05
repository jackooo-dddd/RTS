# `arrivals_between_sub`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_between_sub`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_sub`
- Certificate: `arrivals_between_sub_correspondence`

## Official Rocq

```coq
arrivals_between_sub :
forall {Job : JobType} (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t1 t1' t2 t2' : nat),
is_true (t1' <= t1) ->
is_true (t2 <= t2') ->
is_true (j \in @arrivals_between Job arr_seq t1 t2) -> is_true (j \in @arrivals_between Job arr_seq t1' t2')

arrivals_between_sub is not universe polymorphic
Arguments arrivals_between_sub {Job} arr_seq j (t1 t1' t2 t2')%nat_scope _ _ _
arrivals_between_sub is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_between_sub
Declared in library prosa.analysis.facts.behavior.arrivals, line 169, characters 8-28
@arrivals_between_sub
     : forall (Job : JobType) (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t1 t1' t2 t2' : nat),
       is_true (t1' <= t1) ->
       is_true (t2 <= t2') ->
       is_true (j \in @arrivals_between Job arr_seq t1 t2) ->
       is_true (j \in @arrivals_between Job arr_seq t1' t2')
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_sub : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (j : Job)
  (t1 t1' t2 t2' : ℕ),
  t1' ≤ t1 →
    t2 ≤ t2' →
      decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true →
        decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1' t2') = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_sub
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (j : Job) (t1 t1' t2 t2' : Nat),
       LE_le_inst1 Nat instLENat t1' t1 ->
       LE_le_inst1 Nat instLENat t2 t2' ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1 t2)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1 t2)))
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1' t2')
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1' t2')))
         Bool_true
```
