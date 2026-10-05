# `arrived_between_implies_in_arrivals`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrived_between_implies_in_arrivals`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals`
- Certificate: `arrived_between_implies_in_arrivals_correspondence`

## Official Rocq

```coq
arrived_between_implies_in_arrivals :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (j : Equality.sort Job) (t1 t2 : instant),
@arrives_in Job arr_seq j ->
is_true (@arrived_between Job H j t1 t2) -> is_true (j \in @arrivals_between Job arr_seq t1 t2)

arrived_between_implies_in_arrivals is not universe polymorphic
Arguments arrived_between_implies_in_arrivals {Job H} arr_seq H_consistent_arrival_times j t1 t2 _ _
arrived_between_implies_in_arrivals is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrived_between_implies_in_arrivals
Declared in library prosa.analysis.facts.behavior.arrivals, line 324, characters 10-45
@arrived_between_implies_in_arrivals
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (j : Equality.sort Job) (t1 t2 : instant),
       @arrives_in Job arr_seq j ->
       is_true (@arrived_between Job H j t1 t2) -> is_true (j \in @arrivals_between Job arr_seq t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Behavior.Arrival_sequence.arrived_between j t1 t2 = true →
          decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrived_between_implies_in_arrivals
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
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_arrived_between Job
            inst_3
            inst_6 j t1 t2)
         Bool_true ->
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
         Bool_true
```
