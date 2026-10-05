# `remaining_cost_positive`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.remaining_cost_positive`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.remaining_cost_positive`
- Certificate: `remaining_cost_positive_correspondence`

## Official Rocq

```coq
remaining_cost_positive :
forall {Job : JobType} (online_sched : @schedule Job (ideal.processor_state Job))
  (online_job_cost job_cost_bound : JobCost Job),
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
forall (j : Equality.sort Job) (t : instant),
is_true (~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t) ->
is_true (0 < @remaining_cost_bound Job online_sched job_cost_bound j t)

remaining_cost_positive is not universe polymorphic
Arguments remaining_cost_positive {Job} online_sched online_job_cost job_cost_bound
  H_job_cost_bounded%function_scope j t _
remaining_cost_positive is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.remaining_cost_positive
Declared in library prosa.results.transfer_schedulability.criterion, line 317, characters 10-33
@remaining_cost_positive
     : forall (Job : JobType) (online_sched : @schedule Job (ideal.processor_state Job))
         (online_job_cost job_cost_bound : JobCost Job),
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t) ->
       is_true (0 < @remaining_cost_bound Job online_sched job_cost_bound j t)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.remaining_cost_positive : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (online_job_cost job_cost_bound : Prosa.Behavior.Job.JobCost Job),
  (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      (!Prosa.Behavior.Service.completed_by online_sched j t) = true →
        0 < Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j t
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_remaining_cost_positive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (online_job_cost
          job_cost_bound : Prosa_Behavior_Job_JobCost Job
                             inst_3),
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             online_job_cost j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             job_cost_bound j)) ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               online_sched online_job_cost j t))
         Bool_true ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
            inst_3 online_sched
            job_cost_bound j t)
```
