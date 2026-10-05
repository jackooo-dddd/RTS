# `ref_transfer_schedulability_criterion_ensures_schedulability`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_ensures_schedulability`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.ref_transfer_schedulability_criterion_ensures_schedulability`
- Certificate: `ref_transfer_schedulability_criterion_ensures_schedulability_correspondence`

## Official Rocq

```coq
ref_transfer_schedulability_criterion_ensures_schedulability :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobDeadline Job}
  (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) ref_sched arr_seq ->
@jobs_must_arrive_to_execute Job H (ideal.processor_state Job) ref_sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) ref_sched ref_job_cost ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
(forall j : Equality.sort Job, is_true (online_job_cost j <= ref_job_cost j)) ->
@transfer_schedulability_criterion Job ref_sched online_sched ref_job_cost online_job_cost arr_seq
  ref_job_cost ->
forall j : Equality.sort Job,
is_true (@job_meets_deadline Job (ideal.processor_state Job) ref_sched ref_job_cost H0 j) ->
is_true (@job_meets_deadline Job (ideal.processor_state Job) online_sched online_job_cost H0 j)

ref_transfer_schedulability_criterion_ensures_schedulability is not universe polymorphic
Arguments ref_transfer_schedulability_criterion_ensures_schedulability {Job H H0} 
  ref_sched online_sched ref_job_cost online_job_cost arr_seq H_valid_arrivals H_jobs_arr_ref
  H_jobs_must_arrive_ref H_jobs_exec_ref H_jobs_exec_on H_bounded_job_costs%function_scope 
  _ j _
ref_transfer_schedulability_criterion_ensures_schedulability is opaque
Expands to: Constant
            prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_ensures_schedulability
Declared in library prosa.results.transfer_schedulability.criterion, line 1277, characters 12-72
@ref_transfer_schedulability_criterion_ensures_schedulability
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobDeadline Job)
         (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) ref_sched arr_seq ->
       @jobs_must_arrive_to_execute Job H (ideal.processor_state Job) ref_sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) ref_sched ref_job_cost ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
       (forall j : Equality.sort Job, is_true (online_job_cost j <= ref_job_cost j)) ->
       @transfer_schedulability_criterion Job ref_sched online_sched ref_job_cost online_job_cost arr_seq
         ref_job_cost ->
       forall j : Equality.sort Job,
       is_true (@job_meets_deadline Job (ideal.processor_state Job) ref_sched ref_job_cost H0 j) ->
       is_true (@job_meets_deadline Job (ideal.processor_state Job) online_sched online_job_cost H0 j)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.ref_transfer_schedulability_criterion_ensures_schedulability : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
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
                  ref_job_cost online_job_cost arr_seq ref_job_cost →
                ∀ (j : Job),
                  Prosa.Behavior.Service.job_meets_deadline ref_sched j = true →
                    Prosa.Behavior.Service.job_meets_deadline online_sched j = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_ref_transfer_schedulability_criterion_ensures_schedulability
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
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
         online_sched ref_job_cost online_job_cost arr_seq ref_job_cost ->
       forall j : Job,
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            ref_sched ref_job_cost
            inst_9 j)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            online_sched online_job_cost
            inst_9 j)
         Bool_true
```
