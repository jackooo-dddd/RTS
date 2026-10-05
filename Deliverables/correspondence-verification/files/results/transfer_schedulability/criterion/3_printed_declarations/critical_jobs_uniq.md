# `critical_jobs_uniq`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.critical_jobs_uniq`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.critical_jobs_uniq`
- Certificate: `critical_jobs_uniq_correspondence`

## Official Rocq

```coq
critical_jobs_uniq :
forall {Job : JobType} {H : JobArrival Job}
  (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall t1 t2 : instant,
is_true (@uniq Job (@critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2))

critical_jobs_uniq is not universe polymorphic
Arguments critical_jobs_uniq {Job H} ref_sched online_sched ref_job_cost online_job_cost 
  arr_seq H_valid_arrivals t1 t2
critical_jobs_uniq is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.critical_jobs_uniq
Declared in library prosa.results.transfer_schedulability.criterion, line 441, characters 10-28
@critical_jobs_uniq
     : forall (Job : JobType) (H : JobArrival Job)
         (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall t1 t2 : instant,
       is_true
         (@uniq Job (@critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2))
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.critical_jobs_uniq : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      (Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost online_job_cost
          arr_seq t1 t2).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_critical_jobs_uniq
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
       forall t1 t2 : Prosa_Behavior_Time_instant,
       List_Nodup Job
         (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
            inst_3 ref_sched
            online_sched ref_job_cost online_job_cost arr_seq t1 t2)
```
