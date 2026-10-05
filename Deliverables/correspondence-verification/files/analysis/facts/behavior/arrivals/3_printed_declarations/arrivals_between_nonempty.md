# `arrivals_between_nonempty`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_between_nonempty`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_nonempty`
- Certificate: `arrivals_between_nonempty_correspondence`

## Official Rocq

```coq
arrivals_between_nonempty :
forall {Job : JobType} (arr_seq : arrival_sequence Job) (t1 t2 : instant) (j : Equality.sort Job),
is_true (j \in @arrivals_between Job arr_seq t1 t2) -> is_true (t1 < t2)

arrivals_between_nonempty is not universe polymorphic
Arguments arrivals_between_nonempty {Job} arr_seq t1 t2 j _
arrivals_between_nonempty is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_between_nonempty
Declared in library prosa.analysis.facts.behavior.arrivals, line 378, characters 14-39
@arrivals_between_nonempty
     : forall (Job : JobType) (arr_seq : arrival_sequence Job) (t1 t2 : instant) (j : Equality.sort Job),
       is_true (j \in @arrivals_between Job arr_seq t1 t2) -> is_true (t1 < t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_nonempty : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
  decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true → t1 < t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_nonempty
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (t1 t2 : Prosa_Behavior_Time_instant) (j : Job),
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
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t2
```
