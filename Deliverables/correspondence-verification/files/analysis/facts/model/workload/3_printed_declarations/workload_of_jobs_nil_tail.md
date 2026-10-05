# `workload_of_jobs_nil_tail`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs_nil_tail`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_nil_tail`
- Certificate: `workload_of_jobs_nil_tail_correspondence`

## Official Rocq

```coq
workload_of_jobs_nil_tail :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H1 arr_seq ->
forall {P : Equality.sort Job -> bool} {t1 : instant} {t2 t : nat},
is_true (t <= t2) ->
(forall j : Equality.sort Job,
 is_true (j \in @arrivals_between Job arr_seq t1 t2) ->
 is_true (t <= @job_arrival Job H1 j) -> is_true (~~ P j)) ->
@workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t2) =
@workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t)

workload_of_jobs_nil_tail is not universe polymorphic
Arguments workload_of_jobs_nil_tail {Job H1 H2} arr_seq H_consistent {P}%function_scope 
  {t1} {t2 t}%nat_scope _ _%function_scope
workload_of_jobs_nil_tail is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs_nil_tail
Declared in library prosa.analysis.facts.model.workload, line 239, characters 8-33
@workload_of_jobs_nil_tail
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H1 arr_seq ->
       forall (P : Equality.sort Job -> bool) (t1 : instant) (t2 t : nat),
       is_true (t <= t2) ->
       (forall j : Equality.sort Job,
        is_true (j \in @arrivals_between Job arr_seq t1 t2) ->
        is_true (t <= @job_arrival Job H1 j) -> is_true (~~ P j)) ->
       @workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t2) =
       @workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_nil_tail : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (P : Job → Bool) (t1 : Prosa.Behavior.Time.instant) (t2 t : ℕ),
      t ≤ t2 →
        (∀ (j : Job),
            decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true →
              t ≤ Prosa.Behavior.Job.job_arrival j → (!P j) = true) →
          Prosa.Model.Aggregate.Workload.workload_of_jobs P
              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) =
            Prosa.Model.Aggregate.Workload.workload_of_jobs P
              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_nil_tail
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_6 arr_seq ->
       forall (P : Job -> Bool) (t1 : Prosa_Behavior_Time_instant) (t2 t : Nat),
       LE_le_inst1 Nat instLENat t t2 ->
       (forall j : Job,
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
        LE_le_inst1 Nat instLENat t
          (Prosa_Behavior_Job_JobArrival_job_arrival Job
             inst_3
             inst_6 j) ->
        @eq Bool (Bool_not (P j)) Bool_true) ->
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_9 P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2))
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_9 P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t))
```
