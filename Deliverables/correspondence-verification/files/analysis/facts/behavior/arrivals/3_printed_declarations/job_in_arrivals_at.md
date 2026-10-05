# `job_in_arrivals_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.job_in_arrivals_at`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.job_in_arrivals_at`
- Certificate: `job_in_arrivals_at_correspondence`

## Official Rocq

```coq
job_in_arrivals_at :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j -> @job_arrival Job H j = t -> is_true (j \in @arrivals_at Job arr_seq t)

job_in_arrivals_at is not universe polymorphic
Arguments job_in_arrivals_at {Job H} arr_seq H_consistent_arrival_times j t _ _
job_in_arrivals_at is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.job_in_arrivals_at
Declared in library prosa.analysis.facts.behavior.arrivals, line 208, characters 10-28
@job_in_arrivals_at
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (j : Equality.sort Job) (t : instant),
       @arrives_in Job arr_seq j -> @job_arrival Job H j = t -> is_true (j \in @arrivals_at Job arr_seq t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.job_in_arrivals_at : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Behavior.Job.job_arrival j = t → decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_at arr_seq t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_job_in_arrivals_at
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
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Prosa_Behavior_Time_instant
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j)
         t ->
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
         Bool_true
```
