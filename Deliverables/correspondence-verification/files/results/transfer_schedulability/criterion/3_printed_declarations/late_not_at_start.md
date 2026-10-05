# `late_not_at_start`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.late_not_at_start`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.late_not_at_start`
- Certificate: `late_not_at_start_correspondence`

## Official Rocq

```coq
late_not_at_start :
forall {Job : JobType} (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost job_cost_bound : JobCost Job),
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
(forall j : Equality.sort Job, is_true (job_cost_bound j <= ref_job_cost j)) ->
forall (j : Equality.sort Job) (t : instant),
is_true (@completed_by Job (ideal.processor_state Job) ref_sched ref_job_cost j t) ->
is_true (~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t) ->
is_true (0 < t)

late_not_at_start is not universe polymorphic
Arguments late_not_at_start {Job} ref_sched online_sched ref_job_cost online_job_cost 
  job_cost_bound (H_job_cost_bounded H_ref_cost_dominates)%function_scope j t _ _
late_not_at_start is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.late_not_at_start
Declared in library prosa.results.transfer_schedulability.criterion, line 643, characters 10-27
@late_not_at_start
     : forall (Job : JobType) (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost job_cost_bound : JobCost Job),
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       (forall j : Equality.sort Job, is_true (job_cost_bound j <= ref_job_cost j)) ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@completed_by Job (ideal.processor_state Job) ref_sched ref_job_cost j t) ->
       is_true (~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t) ->
       is_true (0 < t)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.late_not_at_start : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost job_cost_bound : Prosa.Behavior.Job.JobCost Job),
  (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
    (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
      ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Service.completed_by ref_sched j t = true →
          (!Prosa.Behavior.Service.completed_by online_sched j t) = true → 0 < t
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_late_not_at_start
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (ref_sched
          online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (ref_job_cost online_job_cost
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
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             job_cost_bound j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3 ref_job_cost
             j)) ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_completed_by_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            ref_sched ref_job_cost j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               online_sched online_job_cost j t))
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t
```
