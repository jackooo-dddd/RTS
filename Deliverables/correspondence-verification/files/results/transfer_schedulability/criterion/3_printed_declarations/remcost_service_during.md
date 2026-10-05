# `remcost_service_during`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.remcost_service_during`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.remcost_service_during`
- Certificate: `remcost_service_during_correspondence`

## Official Rocq

```coq
remcost_service_during :
forall {Job : JobType} (online_sched : @schedule Job (ideal.processor_state Job))
  (online_job_cost : JobCost Job),
@completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
forall job_cost_bound : JobCost Job,
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
forall (j : Equality.sort Job) (t1 t2 : nat),
is_true (t1 <= t2) ->
@remaining_cost_bound Job online_sched job_cost_bound j t1 =
@remaining_cost_bound Job online_sched job_cost_bound j t2 +
@service_during Job (ideal.processor_state Job) online_sched j t1 t2

remcost_service_during is not universe polymorphic
Arguments remcost_service_during {Job} online_sched online_job_cost H_jobs_exec_on 
  job_cost_bound H_job_cost_bounded%function_scope j (t1 t2)%nat_scope _
remcost_service_during is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.remcost_service_during
Declared in library prosa.results.transfer_schedulability.criterion, line 230, characters 10-32
@remcost_service_during
     : forall (Job : JobType) (online_sched : @schedule Job (ideal.processor_state Job))
         (online_job_cost : JobCost Job),
       @completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
       forall job_cost_bound : JobCost Job,
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       forall (j : Equality.sort Job) (t1 t2 : nat),
       is_true (t1 <= t2) ->
       @remaining_cost_bound Job online_sched job_cost_bound j t1 =
       @remaining_cost_bound Job online_sched job_cost_bound j t2 +
       @service_during Job (ideal.processor_state Job) online_sched j t1 t2
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.remcost_service_during : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (online_job_cost : Prosa.Behavior.Job.JobCost Job),
  Prosa.Behavior.Ready.completed_jobs_dont_execute online_sched →
    ∀ (job_cost_bound : Prosa.Behavior.Job.JobCost Job),
      (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
        ∀ (j : Job) (t1 t2 : ℕ),
          t1 ≤ t2 →
            Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j t1 =
              Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j t2 +
                Prosa.Behavior.Service.service_during online_sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_remcost_service_during
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (online_job_cost : Prosa_Behavior_Job_JobCost Job
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
       forall (j : Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t2 ->
       @eq Nat
         (Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
            inst_3 online_sched
            job_cost_bound j t1)
         (HAdd_hAdd_inst7 Nat Prosa_Behavior_Job_work Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
               inst_3
               online_sched job_cost_bound j t2)
            (Prosa_Behavior_Service_service_during_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               online_sched j t1 t2))
```
