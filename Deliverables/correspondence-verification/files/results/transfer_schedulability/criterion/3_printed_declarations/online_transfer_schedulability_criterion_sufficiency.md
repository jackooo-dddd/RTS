# `online_transfer_schedulability_criterion_sufficiency`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_sufficiency`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.online_transfer_schedulability_criterion_sufficiency`
- Certificate: `online_transfer_schedulability_criterion_sufficiency_correspondence`

## Official Rocq

```coq
online_transfer_schedulability_criterion_sufficiency :
forall {Job : JobType} {H : JobArrival Job}
  (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) ref_sched arr_seq ->
@jobs_must_arrive_to_execute Job H (ideal.processor_state Job) ref_sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) ref_sched ref_job_cost ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
(forall j : Equality.sort Job, is_true (online_job_cost j <= ref_job_cost j)) ->
@transfer_schedulability_criterion Job ref_sched online_sched ref_job_cost online_job_cost arr_seq
  online_job_cost ->
@schedulability_transferred Job ref_sched online_sched ref_job_cost online_job_cost

online_transfer_schedulability_criterion_sufficiency is not universe polymorphic
Arguments online_transfer_schedulability_criterion_sufficiency {Job H} ref_sched 
  online_sched ref_job_cost online_job_cost arr_seq H_valid_arrivals H_jobs_arr_ref 
  H_jobs_must_arrive_ref H_jobs_exec_ref H_jobs_exec_on H_bounded_job_costs%function_scope 
  _ j t _
online_transfer_schedulability_criterion_sufficiency is opaque
Expands to: Constant
            prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_sufficiency
Declared in library prosa.results.transfer_schedulability.criterion, line 1103, characters 10-62
@online_transfer_schedulability_criterion_sufficiency
     : forall (Job : JobType) (H : JobArrival Job)
         (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) ref_sched arr_seq ->
       @jobs_must_arrive_to_execute Job H (ideal.processor_state Job) ref_sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) ref_sched ref_job_cost ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
       (forall j : Equality.sort Job, is_true (online_job_cost j <= ref_job_cost j)) ->
       @transfer_schedulability_criterion Job ref_sched online_sched ref_job_cost online_job_cost arr_seq
         online_job_cost ->
       @schedulability_transferred Job ref_sched online_sched ref_job_cost online_job_cost
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.online_transfer_schedulability_criterion_sufficiency : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Behavior.Ready.jobs_come_from_arrival_sequence ref_sched arr_seq →
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute ref_sched →
        Prosa.Behavior.Ready.completed_jobs_dont_execute ref_sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute online_sched →
            (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
              Prosa.Results.TransferSchedulability.Criterion.transfer_schedulability_criterion ref_sched online_sched
                  ref_job_cost online_job_cost arr_seq online_job_cost →
                Prosa.Results.TransferSchedulability.Criterion.schedulability_transferred ref_sched online_sched
                  ref_job_cost online_job_cost
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_online_transfer_schedulability_criterion_sufficiency
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
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         ref_sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         ref_sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         ref_sched ref_job_cost ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         online_sched online_job_cost ->
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             online_job_cost j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3 ref_job_cost
             j)) ->
       Prosa_Results_TransferSchedulability_Criterion_transfer_schedulability_criterion Job
         inst_3 ref_sched
         online_sched ref_job_cost online_job_cost arr_seq online_job_cost ->
       Prosa_Results_TransferSchedulability_Criterion_schedulability_transferred Job
         inst_3 ref_sched
         online_sched ref_job_cost online_job_cost
```
