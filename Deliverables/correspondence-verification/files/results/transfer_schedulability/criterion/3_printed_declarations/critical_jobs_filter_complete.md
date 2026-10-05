# `critical_jobs_filter_complete`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.critical_jobs_filter_complete`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.critical_jobs_filter_complete`
- Certificate: `critical_jobs_filter_complete_correspondence`

## Official Rocq

```coq
critical_jobs_filter_complete :
forall {Job : JobType} (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) (t1 t2 : nat) 
  (t3 : instant),
is_true (t1 <= t2) ->
@critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3 =
   | ~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t2]

critical_jobs_filter_complete is not universe polymorphic
Arguments critical_jobs_filter_complete {Job} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq (t1 t2)%nat_scope t3 _
critical_jobs_filter_complete is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.critical_jobs_filter_complete
Declared in library prosa.results.transfer_schedulability.criterion, line 419, characters 10-39
@critical_jobs_filter_complete
     : forall (Job : JobType) (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) 
         (t1 t2 : nat) (t3 : instant),
       is_true (t1 <= t2) ->
       @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3 =
       [seq j <- @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3
          | ~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t2]
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.critical_jobs_filter_complete : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (t1 t2 : ℕ) (t3 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost online_job_cost
        arr_seq t2 t3 =
      List.filter (fun j => !Prosa.Behavior.Service.completed_by online_sched j t2)
        (Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
          online_job_cost arr_seq t1 t3)
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_critical_jobs_filter_complete
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
                      inst_3)
         (t1 t2 : Nat) (t3 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Nat instLENat t1 t2 ->
       @eq (List Job)
         (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
            inst_3 ref_sched
            online_sched ref_job_cost online_job_cost arr_seq t2 t3)
         (List_filter Job
            (fun j : Job =>
             Bool_not
               (Prosa_Behavior_Service_completed_by_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  online_sched online_job_cost j t2))
            (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
               inst_3 ref_sched
               online_sched ref_job_cost online_job_cost arr_seq t1 t3))
```
