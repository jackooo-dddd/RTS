# `critical_jobs_min_completion_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.critical_jobs_min_completion_time`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.critical_jobs_min_completion_time`
- Certificate: `critical_jobs_min_completion_time_correspondence`

## Official Rocq

```coq
critical_jobs_min_completion_time :
forall {Job : JobType} {H : JobArrival Job}
  (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) ref_sched ref_job_cost ->
forall job_cost_bound : JobCost Job,
(forall j : Equality.sort Job, is_true (job_cost_bound j <= ref_job_cost j)) ->
forall t : instant,
is_true
  (\sum_(j <- @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq 0 t)
      job_cost_bound j <=
   t)

critical_jobs_min_completion_time is not universe polymorphic
Arguments critical_jobs_min_completion_time {Job H} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq H_valid_arrivals H_jobs_exec_ref job_cost_bound H_ref_cost_dominates%function_scope
  t
critical_jobs_min_completion_time is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.critical_jobs_min_completion_time
Declared in library prosa.results.transfer_schedulability.criterion, line 455, characters 10-43
@critical_jobs_min_completion_time
     : forall (Job : JobType) (H : JobArrival Job)
         (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) ref_sched ref_job_cost ->
       forall job_cost_bound : JobCost Job,
       (forall j : Equality.sort Job, is_true (job_cost_bound j <= ref_job_cost j)) ->
       forall t : instant,
       is_true
         (\sum_(j <- @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq 0 t)
             job_cost_bound j <=
          t)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.critical_jobs_min_completion_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Behavior.Ready.completed_jobs_dont_execute ref_sched →
      ∀ (job_cost_bound : Prosa.Behavior.Job.JobCost Job),
        (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
          ∀ (t : Prosa.Behavior.Time.instant),
            (Prosa.Util.Sum.sumSeq
                (Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
                  online_job_cost arr_seq 0 t)
                fun j => Prosa.Behavior.Job.job_cost j) ≤
              t
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_critical_jobs_min_completion_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
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
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         ref_sched ref_job_cost ->
       forall
         job_cost_bound : Prosa_Behavior_Job_JobCost Job
                            inst_3,
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             job_cost_bound j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3 ref_job_cost
             j)) ->
       forall t : Prosa_Behavior_Time_instant,
       LE_le_inst1 Nat instLENat
         (Prosa_Util_Sum_sumSeq Job
            (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
               inst_3 ref_sched
               online_sched ref_job_cost online_job_cost arr_seq
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t)
            (fun j : Job =>
             Prosa_Behavior_Job_JobCost_job_cost Job
               inst_3
               job_cost_bound j))
         t
```
