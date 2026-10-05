# `workload_of_job`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.workload.workload_of_job`
- Lean: `Prosa.Model.Aggregate.Workload.workload_of_job`
- Certificate: `workload_of_job_correspondence`

## Official Rocq

```coq
workload_of_job :
forall {Job : JobType}, JobCost Job -> arrival_sequence Job -> Equality.sort Job -> instant -> instant -> nat

workload_of_job is not universe polymorphic
Arguments workload_of_job {Job H1} arr_seq j t1 t2
workload_of_job is transparent
Expands to: Constant prosa.model.aggregate.workload.workload_of_job
Declared in library prosa.model.aggregate.workload, line 37, characters 13-28
@workload_of_job
     : forall Job : JobType,
       JobCost Job -> arrival_sequence Job -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
workload_of_job =
fun (Job : JobType) (H1 : JobCost Job) (arr_seq : arrival_sequence Job) (j : Equality.sort Job)
  (t1 t2 : instant) =>
@workload_of_jobs Job H1 (xpred1 j) (@arrivals_between Job arr_seq t1 t2)
     : forall {Job : JobType},
       JobCost Job -> arrival_sequence Job -> Equality.sort Job -> instant -> instant -> nat

Arguments workload_of_job {Job H1} arr_seq j t1 t2
```

## Lean

```lean
@Prosa.Model.Aggregate.Workload.workload_of_job : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.Workload.workload_of_job.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] arr_seq j t1 t2 =>
  Prosa.Model.Aggregate.Workload.workload_of_jobs (fun x => decide (x = j))
    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_Workload_workload_of_job
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_Workload_workload_of_job@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                           inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Model_Aggregate_Workload_workload_of_jobs Job
  inst_3
  inst_6
  (fun x : Job =>
   Decidable_decide (@eq Job x j) (inst_3 x j))
  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
     inst_3 arr_seq t1 t2)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_Workload_workload_of_job Job
  inst_3
  inst_6 arr_seq j t1 
  t2
```
