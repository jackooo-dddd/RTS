# `in_arrseq_implies_arrives`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.in_arrseq_implies_arrives`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.in_arrseq_implies_arrives`
- Certificate: `in_arrseq_implies_arrives_correspondence`

## Official Rocq

```coq
in_arrseq_implies_arrives :
forall {Job : JobType} (arr_seq : arrival_sequence Job) (t : instant) (j : Equality.sort Job),
is_true (j \in arr_seq t) -> @arrives_in Job arr_seq j

in_arrseq_implies_arrives is not universe polymorphic
Arguments in_arrseq_implies_arrives {Job} arr_seq t j _
in_arrseq_implies_arrives is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.in_arrseq_implies_arrives
Declared in library prosa.analysis.facts.behavior.arrivals, line 299, characters 10-35
@in_arrseq_implies_arrives
     : forall (Job : JobType) (arr_seq : arrival_sequence Job) (t : instant) (j : Equality.sort Job),
       is_true (j \in arr_seq t) -> @arrives_in Job arr_seq j
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.in_arrseq_implies_arrives : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (t : Prosa.Behavior.Time.instant) (j : Job),
  decide (j ∈ arr_seq t) = true → Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_in_arrseq_implies_arrives
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (t : Prosa_Behavior_Time_instant) (j : Job),
       @eq Bool
         (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) (arr_seq t) j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j (arr_seq t)))
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j
```
