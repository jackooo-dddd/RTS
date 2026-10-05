# `schedulability_transferred`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.criterion.schedulability_transferred`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.schedulability_transferred`
- Certificate: `schedulability_transferred_correspondence`

## Official Rocq

```coq
schedulability_transferred :
forall {Job : JobType},
@schedule Job (ideal.processor_state Job) ->
@schedule Job (ideal.processor_state Job) -> JobCost Job -> JobCost Job -> Prop

schedulability_transferred is not universe polymorphic
Arguments schedulability_transferred {Job} ref_sched online_sched ref_job_cost online_job_cost
schedulability_transferred is transparent
Expands to: Constant prosa.results.transfer_schedulability.criterion.schedulability_transferred
Declared in library prosa.results.transfer_schedulability.criterion, line 133, characters 13-39
@schedulability_transferred
     : forall Job : JobType,
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) -> JobCost Job -> JobCost Job -> Prop
```

Body:

```coq
schedulability_transferred =
fun Job : JobType =>
let PState := ideal.processor_state Job in
fun (ref_sched online_sched : @schedule Job PState) (ref_job_cost online_job_cost : JobCost Job) =>
let ref_completed_by := @completed_by Job PState ref_sched ref_job_cost in
let online_completed_by := @completed_by Job PState online_sched online_job_cost in
forall (j : Equality.sort Job) (t : instant),
is_true (ref_completed_by j t) -> is_true (online_completed_by j t)
     : forall {Job : JobType},
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) -> JobCost Job -> JobCost Job -> Prop

Arguments schedulability_transferred {Job} ref_sched online_sched ref_job_cost online_job_cost
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.schedulability_transferred : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job → Prosa.Behavior.Job.JobCost Job → Prop
```

Body:

```lean
def Prosa.Results.TransferSchedulability.Criterion.schedulability_transferred.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job → Prosa.Behavior.Job.JobCost Job → Prop :=
fun {Job} [DecidableEq Job] ref_sched online_sched ref_job_cost online_job_cost =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Service.completed_by ref_sched j t = true →
      Prosa.Behavior.Service.completed_by online_sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_schedulability_transferred
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Results_TransferSchedulability_Criterion_schedulability_transferred@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (ref_sched
   online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
  (ref_job_cost
   online_job_cost : Prosa_Behavior_Job_JobCost Job
                       inst_3) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
@eq Bool
  (Prosa_Behavior_Service_completed_by_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3)
     ref_sched ref_job_cost j t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_completed_by_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3)
     online_sched online_job_cost j t)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       SProp

Arguments Prosa_Results_TransferSchedulability_Criterion_schedulability_transferred 
  Job inst_3 
  ref_sched online_sched ref_job_cost online_job_cost
```
