# `arrivals_at_sorted`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_at_sorted`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_at_sorted`
- Certificate: `arrivals_at_sorted_correspondence`

## Official Rocq

```coq
arrivals_at_sorted :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall t : instant,
is_true (@sorted (Equality.sort Job) (@by_arrival_times Job H) (@arrivals_at Job arr_seq t))

arrivals_at_sorted is not universe polymorphic
Arguments arrivals_at_sorted {Job H} arr_seq H_consistent_arrival_times t
arrivals_at_sorted is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_at_sorted
Declared in library prosa.analysis.facts.behavior.arrivals, line 423, characters 10-28
@arrivals_at_sorted
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall t : instant,
       is_true (@sorted (Equality.sort Job) (@by_arrival_times Job H) (@arrivals_at Job arr_seq t))
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_at_sorted : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (t : Prosa.Behavior.Time.instant),
      List.IsChain (fun a b => Prosa.Analysis.Facts.Behavior.Arrivals.by_arrival_times a b = true)
        (Prosa.Behavior.Arrival_sequence.arrivals_at arr_seq t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_at_sorted
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
       forall t : Prosa_Behavior_Time_instant,
       List_IsChain Job
         (fun a b : Job =>
          Prosa_Analysis_Facts_Behavior_Arrivals_by_arrival_times Job
            inst_3
            inst_6 a b =
          Bool_true)
         (Prosa_Behavior_Arrival_sequence_arrivals_at Job
            inst_3 arr_seq t)
```
