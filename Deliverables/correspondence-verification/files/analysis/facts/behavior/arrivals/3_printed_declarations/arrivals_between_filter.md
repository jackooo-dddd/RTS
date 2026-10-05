# `arrivals_between_filter`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_between_filter`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_filter`
- Certificate: `arrivals_between_filter_correspondence`

## Official Rocq

```coq
arrivals_between_filter :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (t1 : instant) (t2 t : nat),
is_true (t <= t2) ->
@arrivals_between Job arr_seq t1 t =

arrivals_between_filter is not universe polymorphic
Arguments arrivals_between_filter {Job H} arr_seq H_consistent_arrival_times t1 (t2 t)%nat_scope _
arrivals_between_filter is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_between_filter
Declared in library prosa.analysis.facts.behavior.arrivals, line 262, characters 10-33
@arrivals_between_filter
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (t1 : instant) (t2 t : nat),
       is_true (t <= t2) ->
       @arrivals_between Job arr_seq t1 t =
       [seq j <- @arrivals_between Job arr_seq t1 t2 | @job_arrival Job H j < t]
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_filter : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (t1 : Prosa.Behavior.Time.instant) (t2 t : ℕ),
      t ≤ t2 →
        Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t =
          List.filter (fun j => decide (Prosa.Behavior.Job.job_arrival j < t))
            (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_filter
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
       forall (t1 : Prosa_Behavior_Time_instant) (t2 t : Nat),
       LE_le_inst1 Nat instLENat t t2 ->
       @eq (List Job)
         (Prosa_Behavior_Arrival_sequence_arrivals_between Job
            inst_3 arr_seq t1 t)
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
```
