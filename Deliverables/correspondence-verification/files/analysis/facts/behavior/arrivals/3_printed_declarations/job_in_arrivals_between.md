# `job_in_arrivals_between`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.job_in_arrivals_between`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.job_in_arrivals_between`
- Certificate: `job_in_arrivals_between_correspondence`

## Official Rocq

```coq
job_in_arrivals_between :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (j : Equality.sort Job) (t1 t2 : nat),
@arrives_in Job arr_seq j ->
is_true (t1 <= @job_arrival Job H j) ->
is_true (@job_arrival Job H j < t2) -> is_true (j \in @arrivals_between Job arr_seq t1 t2)

job_in_arrivals_between is not universe polymorphic
Arguments job_in_arrivals_between {Job H} arr_seq H_consistent_arrival_times j (t1 t2)%nat_scope _ _ _
job_in_arrivals_between is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.job_in_arrivals_between
Declared in library prosa.analysis.facts.behavior.arrivals, line 348, characters 10-33
@job_in_arrivals_between
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (j : Equality.sort Job) (t1 t2 : nat),
       @arrives_in Job arr_seq j ->
       is_true (t1 <= @job_arrival Job H j) ->
       is_true (@job_arrival Job H j < t2) -> is_true (j \in @arrivals_between Job arr_seq t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.job_in_arrivals_between : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t1 t2 : ℕ),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        t1 ≤ Prosa.Behavior.Job.job_arrival j →
          Prosa.Behavior.Job.job_arrival j < t2 →
            decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_job_in_arrivals_between
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
       forall (j : Job) (t1 t2 : Nat),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       LE_le_inst1 Nat instLENat t1
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j) ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j)
         t2 ->
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
