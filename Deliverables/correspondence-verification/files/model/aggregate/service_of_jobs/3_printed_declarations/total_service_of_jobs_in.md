# `total_service_of_jobs_in`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in`
- Lean: `Prosa.Model.Aggregate.ServiceOfJobs.total_service_of_jobs_in`
- Certificate: `total_service_of_jobs_in_correspondence`

## Official Rocq

```coq
total_service_of_jobs_in :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> seq (Equality.sort Job) -> instant -> instant -> nat

total_service_of_jobs_in is not universe polymorphic
Arguments total_service_of_jobs_in {Job PState} sched jobs%seq_scope t1 t2
total_service_of_jobs_in is transparent
Expands to: Constant prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in
Declared in library prosa.model.aggregate.service_of_jobs, line 122, characters 15-39
@total_service_of_jobs_in
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> seq (Equality.sort Job) -> instant -> instant -> nat
```

Body:

```coq
total_service_of_jobs_in =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
  (jobs : seq (Equality.sort Job)) (t1 : instant) =>
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> seq (Equality.sort Job) -> instant -> instant -> nat

Arguments total_service_of_jobs_in {Job PState} sched jobs%seq_scope t1 t2
```

## Lean

```lean
@Prosa.Model.Aggregate.ServiceOfJobs.total_service_of_jobs_in : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → List Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.ServiceOfJobs.total_service_of_jobs_in.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        List Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {PState} sched jobs t1 t2 =>
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun x => true) jobs t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       List Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (jobs : List Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
  inst_3 PState sched
  (fun _ : Job => Bool_true) jobs t1 t2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       List Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in Job
  inst_3 PState sched 
  jobs t1 t
```
