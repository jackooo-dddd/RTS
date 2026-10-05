# `service_of_jobs_at`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.service_of_jobs.service_of_jobs_at`
- Lean: `Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at`
- Certificate: `service_of_jobs_at_correspondence`

## Official Rocq

```coq
service_of_jobs_at :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> pred (Equality.sort Job) -> seq (Equality.sort Job) -> instant -> nat

service_of_jobs_at is not universe polymorphic
Arguments service_of_jobs_at {Job PState} sched P jobs%seq_scope t
service_of_jobs_at is transparent
Expands to: Constant prosa.model.aggregate.service_of_jobs.service_of_jobs_at
Declared in library prosa.model.aggregate.service_of_jobs, line 37, characters 15-33
@service_of_jobs_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> pred (Equality.sort Job) -> seq (Equality.sort Job) -> instant -> nat
```

Body:

```coq
service_of_jobs_at =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
  (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t : instant) =>
\sum_(j <- jobs | P j) @service_at Job PState sched j t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> pred (Equality.sort Job) -> seq (Equality.sort Job) -> instant -> nat

Arguments service_of_jobs_at {Job PState} sched P jobs%seq_scope t
```

## Lean

```lean
@Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → (Job → Bool) → List Job → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → (Job → Bool) → List Job → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {PState} sched P jobs t =>
  Prosa.Util.Sum.sumFiltered jobs P fun j => Prosa.Behavior.Service.service_at sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       (Job -> Bool) -> List Job -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (P : Job -> Bool) (jobs : List Job) (t : Prosa_Behavior_Time_instant) =>
Prosa_Util_Sum_sumFiltered Job jobs P
  (fun j : Job =>
   Prosa_Behavior_Service_service_at Job
     inst_3 PState sched j t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       (Job -> Bool) -> List Job -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at Job
  inst_3 PState 
  sched P%_function_scope jobs t
```
