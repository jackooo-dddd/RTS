# `workload_of_job_eq_job_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_job_eq_job_arrival`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_job_eq_job_arrival`
- Certificate: `workload_of_job_eq_job_arrival_correspondence`

## Official Rocq

```coq
workload_of_job_eq_job_arrival :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H1 arr_seq ->
@arrival_sequence_uniq Job arr_seq ->
forall (j : Equality.sort Job) (t1 t2 : instant),
@arrives_in Job arr_seq j ->
@workload_of_job Job H2 arr_seq j t1 t2 =
(if t1 <= @job_arrival Job H1 j < t2 then @job_cost Job H2 j else 0)

workload_of_job_eq_job_arrival is not universe polymorphic
Arguments workload_of_job_eq_job_arrival {Job H1 H2} arr_seq H_consistent H_arrival_sequence_is_a_set 
  j t1 t2 _
workload_of_job_eq_job_arrival is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_job_eq_job_arrival
Declared in library prosa.analysis.facts.model.workload, line 183, characters 10-40
@workload_of_job_eq_job_arrival
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H1 arr_seq ->
       @arrival_sequence_uniq Job arr_seq ->
       forall (j : Equality.sort Job) (t1 t2 : instant),
       @arrives_in Job arr_seq j ->
       @workload_of_job Job H2 arr_seq j t1 t2 =
       (if t1 <= @job_arrival Job H1 j < t2 then @job_cost Job H2 j else 0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_job_eq_job_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq →
      ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
          Prosa.Model.Aggregate.Workload.workload_of_job arr_seq j t1 t2 =
            bif decide (t1 ≤ Prosa.Behavior.Job.job_arrival j) && decide (Prosa.Behavior.Job.job_arrival j < t2) then
              Prosa.Behavior.Job.job_cost j
            else 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_job_eq_job_arrival
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
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_3 arr_seq ->
       forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_job Job
            inst_3
            inst_9 arr_seq j t1 t2)
         (cond Prosa_Behavior_Job_work
            (Bool_and
               (Decidable_decide
                  (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_3
                        inst_6 j))
                  (Nat_decLe t1
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_3
                        inst_6 j)))
               (Decidable_decide
                  (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_3
                        inst_6 j)
                     t2)
                  (Nat_decLt
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_3
                        inst_6 j)
                     t2)))
            (Prosa_Behavior_Job_JobCost_job_cost Job
               inst_3
               inst_9 j)
            (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
```
