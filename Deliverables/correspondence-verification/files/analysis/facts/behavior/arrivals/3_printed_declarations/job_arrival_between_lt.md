# `job_arrival_between_lt`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.arrivals.job_arrival_between_lt`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_lt`
- Certificate: `job_arrival_between_lt_correspondence`

## Official Rocq

```coq
job_arrival_between_lt :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall {j : Equality.sort Job} {t1 t2 : instant},
is_true (j \in @arrivals_between Job arr_seq t1 t2) -> is_true (@job_arrival Job H j < t2)

job_arrival_between_lt is not universe polymorphic
Arguments job_arrival_between_lt {Job H} arr_seq H_consistent_arrival_times {j t1 t2} _
job_arrival_between_lt is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.job_arrival_between_lt
Declared in library prosa.analysis.facts.behavior.arrivals, line 236, characters 14-36
@job_arrival_between_lt
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (j : Equality.sort Job) (t1 t2 : instant),
       is_true (j \in @arrivals_between Job arr_seq t1 t2) -> is_true (@job_arrival Job H j < t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_lt : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true →
        Prosa.Behavior.Job.job_arrival j < t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_between_lt
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
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j)
         t2
```
