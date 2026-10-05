# `arrivals_between_mem_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_between_mem_cat`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_mem_cat`
- Certificate: `arrivals_between_mem_cat_correspondence`

## Official Rocq

```coq
arrivals_between_mem_cat :
forall {Job : JobType} (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t1 t t2 : nat),
is_true (t1 <= t) ->
is_true (t <= t2) ->
(j \in @arrivals_between Job arr_seq t1 t2) =
(j \in @arrivals_between Job arr_seq t1 t ++ @arrivals_between Job arr_seq t t2)

arrivals_between_mem_cat is not universe polymorphic
Arguments arrivals_between_mem_cat {Job} arr_seq j (t1 t t2)%nat_scope _ _
arrivals_between_mem_cat is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_between_mem_cat
Declared in library prosa.analysis.facts.behavior.arrivals, line 158, characters 8-32
@arrivals_between_mem_cat
     : forall (Job : JobType) (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t1 t t2 : nat),
       is_true (t1 <= t) ->
       is_true (t <= t2) ->
       (j \in @arrivals_between Job arr_seq t1 t2) =
       (j \in @arrivals_between Job arr_seq t1 t ++ @arrivals_between Job arr_seq t t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_mem_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (j : Job) (t1 t t2 : ℕ),
  t1 ≤ t →
    t ≤ t2 →
      decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) =
        decide
          (j ∈
            Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t ++
              Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_mem_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (j : Job) (t1 t t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t ->
       LE_le_inst1 Nat instLENat t t2 ->
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
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (HAppend_hAppend (List Job) (List Job) (List Job)
                  (instHAppendOfAppend (List Job) (List_instAppend Job))
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_3 arr_seq t1 t)
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_3 arr_seq t t2))
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (HAppend_hAppend (List Job) (List Job) (List Job)
                  (instHAppendOfAppend (List Job) (List_instAppend Job))
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_3 arr_seq t1 t)
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_3 arr_seq t t2))))
```
