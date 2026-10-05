# `arrivals_between_filter_nil`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_between_filter_nil`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_filter_nil`
- Certificate: `arrivals_between_filter_nil_correspondence`

## Official Rocq

```coq
arrivals_between_filter_nil :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (t1 : nat) (t2 : instant) (t : nat),
is_true (t < t1) -> [seq j <- @arrivals_between Job arr_seq t1 t2 | @job_arrival Job H j < t] = [::]

arrivals_between_filter_nil is not universe polymorphic
Arguments arrivals_between_filter_nil {Job H} arr_seq H_consistent_arrival_times 
  t1%nat_scope t2 t%nat_scope _
arrivals_between_filter_nil is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_between_filter_nil
Declared in library prosa.analysis.facts.behavior.arrivals, line 244, characters 10-37
@arrivals_between_filter_nil
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (t1 : nat) (t2 : instant) (t : nat),
       is_true (t < t1) -> [seq j <- @arrivals_between Job arr_seq t1 t2 | @job_arrival Job H j < t] = [::]
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_filter_nil : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (t1 : ℕ) (t2 : Prosa.Behavior.Time.instant),
      ∀ t < t1,
        List.filter (fun j => decide (Prosa.Behavior.Job.job_arrival j < t))
            (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) =
          []
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_filter_nil
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
       forall (t1 : Nat) (t2 : Prosa_Behavior_Time_instant) (t : Nat),
       LT_lt_inst1 Nat instLTNat t t1 ->
       @eq (List Job)
         (List_filter Job
            (fun j : Job =>
             Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j)
                  t)
               (Nat_decLt
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j)
                  t))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2))
         (List_nil Job)
```
