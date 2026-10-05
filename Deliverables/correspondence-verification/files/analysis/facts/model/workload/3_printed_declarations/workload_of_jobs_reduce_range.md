# `workload_of_jobs_reduce_range`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs_reduce_range`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_reduce_range`
- Certificate: `workload_of_jobs_reduce_range_correspondence`

## Official Rocq

```coq
workload_of_jobs_reduce_range :
forall {Job : JobType} {H2 : JobCost Job} (arr_seq : arrival_sequence Job) (t1 t2 t3 : nat)
  (P : pred (Equality.sort Job)),
is_true (t1 <= t2) ->
is_true (t2 <= t3) ->
is_true
  (@workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t2) <=
   @workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t3))

workload_of_jobs_reduce_range is not universe polymorphic
Arguments workload_of_jobs_reduce_range {Job H2} arr_seq (t1 t2 t3)%nat_scope P _ _
workload_of_jobs_reduce_range is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs_reduce_range
Declared in library prosa.analysis.facts.model.workload, line 270, characters 12-41
@workload_of_jobs_reduce_range
     : forall (Job : JobType) (H2 : JobCost Job) (arr_seq : arrival_sequence Job) 
         (t1 t2 t3 : nat) (P : pred (Equality.sort Job)),
       is_true (t1 <= t2) ->
       is_true (t2 <= t3) ->
       is_true
         (@workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t2) <=
          @workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t3))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_reduce_range : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (t1 t2 t3 : ℕ) (P : Job → Bool),
  t1 ≤ t2 →
    t2 ≤ t3 →
      Prosa.Model.Aggregate.Workload.workload_of_jobs P
          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) ≤
        Prosa.Model.Aggregate.Workload.workload_of_jobs P
          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t3)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_reduce_range
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (t1 t2 t3 : Nat) (P : Job -> Bool),
       LE_le_inst1 Nat instLENat t1 t2 ->
       LE_le_inst1 Nat instLENat t2 t3 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2))
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t3))
```
