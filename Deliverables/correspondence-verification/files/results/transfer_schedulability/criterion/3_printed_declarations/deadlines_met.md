# `deadlines_met`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.transfer_schedulability.criterion.deadlines_met`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.deadlines_met`
- Certificate: `deadlines_met_correspondence`

## Official Rocq

```coq
deadlines_met :
forall {Job : JobType} {H0 : JobDeadline Job}
  (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job),
@schedulability_transferred Job ref_sched online_sched ref_job_cost online_job_cost ->
forall j : Equality.sort Job,
is_true (@job_meets_deadline Job (ideal.processor_state Job) ref_sched ref_job_cost H0 j) ->
is_true (@job_meets_deadline Job (ideal.processor_state Job) online_sched online_job_cost H0 j)

deadlines_met is not universe polymorphic
Arguments deadlines_met {Job H0} ref_sched online_sched ref_job_cost online_job_cost _ j _
deadlines_met is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.deadlines_met
Declared in library prosa.results.transfer_schedulability.criterion, line 149, characters 12-25
@deadlines_met
     : forall (Job : JobType) (H0 : JobDeadline Job)
         (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job),
       @schedulability_transferred Job ref_sched online_sched ref_job_cost online_job_cost ->
       forall j : Equality.sort Job,
       is_true (@job_meets_deadline Job (ideal.processor_state Job) ref_sched ref_job_cost H0 j) ->
       is_true (@job_meets_deadline Job (ideal.processor_state Job) online_sched online_job_cost H0 j)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.deadlines_met : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobDeadline Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job),
  Prosa.Results.TransferSchedulability.Criterion.schedulability_transferred ref_sched online_sched ref_job_cost
      online_job_cost →
    ∀ (j : Job),
      Prosa.Behavior.Service.job_meets_deadline ref_sched j = true →
        Prosa.Behavior.Service.job_meets_deadline online_sched j = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_deadlines_met
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (ref_sched
          online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (ref_job_cost
          online_job_cost : Prosa_Behavior_Job_JobCost Job
                              inst_3),
       Prosa_Results_TransferSchedulability_Criterion_schedulability_transferred Job
         inst_3 ref_sched
         online_sched ref_job_cost online_job_cost ->
       forall j : Job,
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            ref_sched ref_job_cost
            inst_6 j)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            online_sched online_job_cost
            inst_6 j)
         Bool_true
```
