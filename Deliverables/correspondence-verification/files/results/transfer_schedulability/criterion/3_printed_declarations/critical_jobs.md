# `critical_jobs`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.criterion.critical_jobs`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.critical_jobs`
- Certificate: `critical_jobs_correspondence`

## Official Rocq

```coq
critical_jobs :
forall {Job : JobType},
@schedule Job (ideal.processor_state Job) ->
@schedule Job (ideal.processor_state Job) ->
JobCost Job -> JobCost Job -> arrival_sequence Job -> instant -> instant -> seq (Equality.sort Job)

critical_jobs is not universe polymorphic
Arguments critical_jobs {Job} ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2
critical_jobs is transparent
Expands to: Constant prosa.results.transfer_schedulability.criterion.critical_jobs
Declared in library prosa.results.transfer_schedulability.criterion, line 370, characters 15-28
@critical_jobs
     : forall Job : JobType,
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) ->
       JobCost Job -> JobCost Job -> arrival_sequence Job -> instant -> instant -> seq (Equality.sort Job)
```

Body:

```coq
critical_jobs =
fun Job : JobType =>
let PState := ideal.processor_state Job in
fun (ref_sched online_sched : @schedule Job PState) (ref_job_cost online_job_cost : JobCost Job) =>
let ref_completed_by := @completed_by Job PState ref_sched ref_job_cost in
let online_completed_by := @completed_by Job PState online_sched online_job_cost in
fun (arr_seq : arrival_sequence Job) (t1 t2 : instant) =>
     : forall {Job : JobType},
       @schedule Job (ideal.processor_state Job) ->
       @schedule Job (ideal.processor_state Job) ->
       JobCost Job -> JobCost Job -> arrival_sequence Job -> instant -> instant -> seq (Equality.sort Job)

Arguments critical_jobs {Job} ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.critical_jobs : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job →
          Prosa.Behavior.Job.JobCost Job →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → List Job
```

Body:

```lean
def Prosa.Results.TransferSchedulability.Criterion.critical_jobs.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
        Prosa.Behavior.Job.JobCost Job →
          Prosa.Behavior.Job.JobCost Job →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2 =>
  List.filter
    (fun j =>
      Prosa.Behavior.Service.completed_by ref_sched j t2 && !Prosa.Behavior.Service.completed_by online_sched j t1)
    (Prosa.Behavior.Arrival_sequence.arrivals_up_to arr_seq t2)
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_critical_jobs
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
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Results_TransferSchedulability_Criterion_critical_jobs@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
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
  (t1 t2 : Prosa_Behavior_Time_instant) =>
List_filter Job
  (fun j : Job =>
   Bool_and
     (Prosa_Behavior_Service_completed_by_inst4 Job
        inst_3
        (Prosa_Model_Processor_Ideal_processor_state Job
           inst_3)
        ref_sched ref_job_cost j t2)
     (Bool_not
        (Prosa_Behavior_Service_completed_by_inst4 Job
           inst_3
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3)
           online_sched online_job_cost j t1)))
  (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
     inst_3 arr_seq t2)
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
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
  inst_3 
  ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2
```
