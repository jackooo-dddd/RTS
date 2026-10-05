# `in_arrivals_implies_arrived_before`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_before`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_before`
- Certificate: `in_arrivals_implies_arrived_before_correspondence`

## Official Rocq

```coq
in_arrivals_implies_arrived_before :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (j : Equality.sort Job) (t : instant),
is_true (j \in @arrivals_before Job arr_seq t) -> is_true (@arrived_before Job H j t)

in_arrivals_implies_arrived_before is not universe polymorphic
Arguments in_arrivals_implies_arrived_before {Job H} arr_seq H_consistent_arrival_times j t _
in_arrivals_implies_arrived_before is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_before
Declared in library prosa.analysis.facts.behavior.arrivals, line 316, characters 10-44
@in_arrivals_implies_arrived_before
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (j \in @arrivals_before Job arr_seq t) -> is_true (@arrived_before Job H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_before : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_before arr_seq t) = true →
        Prosa.Behavior.Arrival_sequence.arrived_before j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_in_arrivals_implies_arrived_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_6 arr_seq ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_before Job
                  inst_3 arr_seq t)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_before Job
                  inst_3 arr_seq t)))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_arrived_before Job
            inst_3
            inst_6 j t)
         Bool_true
```
