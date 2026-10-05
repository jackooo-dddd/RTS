# `workload_equal_subset`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_equal_subset`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_equal_subset`
- Certificate: `workload_equal_subset_correspondence`

## Official Rocq

```coq
workload_equal_subset :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H1 arr_seq ->
@valid_arrival_sequence Job H1 arr_seq ->
forall (t1 t2 t : instant) (P : pred (Equality.sort Job)),
is_true
  (@workload_of_jobs Job H2 (fun j : Equality.sort Job => (@job_arrival Job H1 j <= t) && P j)
     (@arrivals_between Job arr_seq t1 t2) <=
   @workload_of_jobs Job H2 [eta P] (@arrivals_between Job arr_seq t1 (t + 1)))

workload_equal_subset is not universe polymorphic
Arguments workload_equal_subset {Job H1 H2} arr_seq H_consistent H_valid_arrival_sequence t1 t2 t P
workload_equal_subset is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_equal_subset
Declared in library prosa.analysis.facts.model.workload, line 344, characters 10-31
@workload_equal_subset
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H1 arr_seq ->
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (t1 t2 t : instant) (P : pred (Equality.sort Job)),
       is_true
         (@workload_of_jobs Job H2 (fun j : Equality.sort Job => (@job_arrival Job H1 j <= t) && P j)
            (@arrivals_between Job arr_seq t1 t2) <=
          @workload_of_jobs Job H2 [eta P] (@arrivals_between Job arr_seq t1 (t + 1)))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_equal_subset : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
      ∀ (t1 t2 t : Prosa.Behavior.Time.instant) (P : Job → Bool),
        Prosa.Model.Aggregate.Workload.workload_of_jobs (fun j => decide (Prosa.Behavior.Job.job_arrival j ≤ t) && P j)
            (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) ≤
          Prosa.Model.Aggregate.Workload.workload_of_jobs (fun x => P x)
            (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t + 1))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_equal_subset
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
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall (t1 t2 t : Prosa_Behavior_Time_instant) (P : Job -> Bool),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_9
            (fun j : Job =>
             Bool_and
               (Decidable_decide
                  (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_3
                        inst_6 j)
                     t)
                  (Nat_decLe
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_3
                        inst_6 j)
                     t))
               (P j))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2))
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_9 
            (fun x : Job => P x)
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))))
```
