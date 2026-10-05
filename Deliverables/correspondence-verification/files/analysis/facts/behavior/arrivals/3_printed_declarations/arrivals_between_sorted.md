# `arrivals_between_sorted`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_between_sorted`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_sorted`
- Certificate: `arrivals_between_sorted_correspondence`

## Official Rocq

```coq
arrivals_between_sorted :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall t1 t2 : instant,
is_true (@sorted (Equality.sort Job) (@by_arrival_times Job H) (@arrivals_between Job arr_seq t1 t2))

arrivals_between_sorted is not universe polymorphic
Arguments arrivals_between_sorted {Job H} arr_seq H_consistent_arrival_times t1 t2
arrivals_between_sorted is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_between_sorted
Declared in library prosa.analysis.facts.behavior.arrivals, line 439, characters 10-33
@arrivals_between_sorted
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall t1 t2 : instant,
       is_true (@sorted (Equality.sort Job) (@by_arrival_times Job H) (@arrivals_between Job arr_seq t1 t2))
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_sorted : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      List.IsChain (fun a b => Prosa.Analysis.Facts.Behavior.Arrivals.by_arrival_times a b = true)
        (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_sorted
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
       forall t1 t2 : Prosa_Behavior_Time_instant,
       List_IsChain Job
         (fun a b : Job =>
          Prosa_Analysis_Facts_Behavior_Arrivals_by_arrival_times Job
            inst_3
            inst_6 a b =
          Bool_true)
         (Prosa_Behavior_Arrival_sequence_arrivals_between Job
            inst_3 arr_seq t1 t2)
```
