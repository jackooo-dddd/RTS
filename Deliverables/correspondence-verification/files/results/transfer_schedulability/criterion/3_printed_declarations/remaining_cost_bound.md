# `remaining_cost_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.criterion.remaining_cost_bound`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound`
- Certificate: `remaining_cost_bound_correspondence`

## Official Rocq

```coq
remaining_cost_bound :
forall {Job : JobType},
@schedule Job (ideal.processor_state Job) -> JobCost Job -> Equality.sort Job -> instant -> nat

remaining_cost_bound is not universe polymorphic
Arguments remaining_cost_bound {Job} online_sched job_cost_bound j t
remaining_cost_bound is transparent
Expands to: Constant prosa.results.transfer_schedulability.criterion.remaining_cost_bound
Declared in library prosa.results.transfer_schedulability.criterion, line 204, characters 15-35
@remaining_cost_bound
     : forall Job : JobType,
       @schedule Job (ideal.processor_state Job) -> JobCost Job -> Equality.sort Job -> instant -> nat
```

Body:

```coq
remaining_cost_bound =
fun Job : JobType =>
let PState := ideal.processor_state Job in
fun (online_sched : @schedule Job PState) (job_cost_bound : JobCost Job) (j : Equality.sort Job)
  (t : instant) =>
job_cost_bound j - @service Job PState online_sched j t
     : forall {Job : JobType},
       @schedule Job (ideal.processor_state Job) -> JobCost Job -> Equality.sort Job -> instant -> nat

Arguments remaining_cost_bound {Job} online_sched job_cost_bound j t
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Job.JobCost Job → Job → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Job.JobCost Job → Job → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] online_sched job_cost_bound j t =>
  Prosa.Behavior.Job.job_cost j - Prosa.Behavior.Service.service online_sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
  (job_cost_bound : Prosa_Behavior_Job_JobCost Job
                      inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
HSub_hSub_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
  (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3 job_cost_bound j)
  (Prosa_Behavior_Service_service_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3)
     online_sched j t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
  inst_3 
  online_sched job_cost_bound j t
```
