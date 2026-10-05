# `job_arrival_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.job_arrival_at`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_at`
- Certificate: `job_arrival_at_correspondence`

## Official Rocq

```coq
job_arrival_at :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall {j : Equality.sort Job} {t : instant},
is_true (j \in @arrivals_at Job arr_seq t) -> @job_arrival Job H j = t

job_arrival_at is not universe polymorphic
Arguments job_arrival_at {Job H} arr_seq H_consistent_arrival_times {j t} _
job_arrival_at is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.job_arrival_at
Declared in library prosa.analysis.facts.behavior.arrivals, line 201, characters 10-24
@job_arrival_at
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (j \in @arrivals_at Job arr_seq t) -> @job_arrival Job H j = t
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_at : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_at arr_seq t) = true → Prosa.Behavior.Job.job_arrival j = t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_at
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
               (Prosa_Behavior_Arrival_sequence_arrivals_at Job
                  inst_3 arr_seq t)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_at Job
                  inst_3 arr_seq t)))
         Bool_true ->
       @eq Prosa_Behavior_Time_instant
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j)
         t
```
