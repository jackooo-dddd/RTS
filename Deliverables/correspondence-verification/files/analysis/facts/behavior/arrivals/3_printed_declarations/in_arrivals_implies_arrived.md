# `in_arrivals_implies_arrived`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived`
- Certificate: `in_arrivals_implies_arrived_correspondence`

## Official Rocq

```coq
in_arrivals_implies_arrived :
forall {Job : JobType} (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t1 t2 : instant),
is_true (j \in @arrivals_between Job arr_seq t1 t2) -> @arrives_in Job arr_seq j

in_arrivals_implies_arrived is not universe polymorphic
Arguments in_arrivals_implies_arrived {Job} arr_seq j t1 t2 _
in_arrivals_implies_arrived is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived
Declared in library prosa.analysis.facts.behavior.arrivals, line 292, characters 10-37
@in_arrivals_implies_arrived
     : forall (Job : JobType) (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t1 t2 : instant),
       is_true (j \in @arrivals_between Job arr_seq t1 t2) -> @arrives_in Job arr_seq j
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (j : Job)
  (t1 t2 : Prosa.Behavior.Time.instant),
  decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true →
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_in_arrivals_implies_arrived
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
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
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j
```
