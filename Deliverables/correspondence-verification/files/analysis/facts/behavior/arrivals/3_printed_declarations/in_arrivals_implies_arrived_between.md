# `in_arrivals_implies_arrived_between`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_between`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_between`
- Certificate: `in_arrivals_implies_arrived_between_correspondence`

## Official Rocq

```coq
in_arrivals_implies_arrived_between :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (j : Equality.sort Job) (t1 t2 : instant),
is_true (j \in @arrivals_between Job arr_seq t1 t2) -> is_true (@arrived_between Job H j t1 t2)

in_arrivals_implies_arrived_between is not universe polymorphic
Arguments in_arrivals_implies_arrived_between {Job H} arr_seq H_consistent_arrival_times j t1 t2 _
in_arrivals_implies_arrived_between is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_between
Declared in library prosa.analysis.facts.behavior.arrivals, line 308, characters 10-45
@in_arrivals_implies_arrived_between
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (j : Equality.sort Job) (t1 t2 : instant),
       is_true (j \in @arrivals_between Job arr_seq t1 t2) -> is_true (@arrived_between Job H j t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_between : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true →
        Prosa.Behavior.Arrival_sequence.arrived_between j t1 t2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_in_arrivals_implies_arrived_between
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
       forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
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
         (Prosa_Behavior_Arrival_sequence_arrived_between Job
            inst_3
            inst_6 j t1 t2)
         Bool_true
```
