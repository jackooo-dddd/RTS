# `critical_jobs_remaining_cost_monotonic`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.critical_jobs_remaining_cost_monotonic`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.critical_jobs_remaining_cost_monotonic`
- Certificate: `critical_jobs_remaining_cost_monotonic_correspondence`

## Official Rocq

```coq
critical_jobs_remaining_cost_monotonic :
forall {Job : JobType} (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
@completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
forall job_cost_bound : JobCost Job,
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
forall t1 t2 t3 : nat,
is_true (t1 <= t2 <= t3) ->
is_true
  (\sum_(j <- @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3)
      @remaining_cost_bound Job online_sched job_cost_bound j t2 <=
   \sum_(j <- @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3)
      @remaining_cost_bound Job online_sched job_cost_bound j t1)

critical_jobs_remaining_cost_monotonic is not universe polymorphic
Arguments critical_jobs_remaining_cost_monotonic {Job} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq H_jobs_exec_on job_cost_bound H_job_cost_bounded%function_scope
  (t1 t2 t3)%nat_scope _
critical_jobs_remaining_cost_monotonic is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.critical_jobs_remaining_cost_monotonic
Declared in library prosa.results.transfer_schedulability.criterion, line 479, characters 10-48
@critical_jobs_remaining_cost_monotonic
     : forall (Job : JobType) (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
       forall job_cost_bound : JobCost Job,
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       forall t1 t2 t3 : nat,
       is_true (t1 <= t2 <= t3) ->
       is_true
         (\sum_(j <- @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3)
             @remaining_cost_bound Job online_sched job_cost_bound j t2 <=
          \sum_(j <- @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3)
             @remaining_cost_bound Job online_sched job_cost_bound j t1)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.critical_jobs_remaining_cost_monotonic : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Ready.completed_jobs_dont_execute online_sched →
    ∀ (job_cost_bound : Prosa.Behavior.Job.JobCost Job),
      (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
        ∀ (t1 t2 t3 : ℕ),
          (decide (t1 ≤ t2) && decide (t2 ≤ t3)) = true →
            (Prosa.Util.Sum.sumSeq
                (Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
                  online_job_cost arr_seq t2 t3)
                fun j =>
                Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j t2) ≤
              Prosa.Util.Sum.sumSeq
                (Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
                  online_job_cost arr_seq t1 t3)
                fun j =>
                Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j t1
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_critical_jobs_remaining_cost_monotonic
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (ref_sched
          online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (ref_job_cost
          online_job_cost : Prosa_Behavior_Job_JobCost Job
                              inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         online_sched online_job_cost ->
       forall
         job_cost_bound : Prosa_Behavior_Job_JobCost Job
                            inst_3,
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             online_job_cost j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             job_cost_bound j)) ->
       forall t1 t2 t3 : Nat,
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t2) (Nat_decLe t1 t2))
            (Decidable_decide (LE_le_inst1 Nat instLENat t2 t3) (Nat_decLe t2 t3)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Util_Sum_sumSeq Job
            (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
               inst_3 ref_sched
               online_sched ref_job_cost online_job_cost arr_seq t2 t3)
            (fun j : Job =>
             Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
               inst_3
               online_sched job_cost_bound j t2))
         (Prosa_Util_Sum_sumSeq Job
            (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
               inst_3 ref_sched
               online_sched ref_job_cost online_job_cost arr_seq t1 t3)
            (fun j : Job =>
             Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
               inst_3
               online_sched job_cost_bound j t1))
```
