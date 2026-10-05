# `workload_of_jobs`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.workload.workload_of_jobs`
- Lean: `Prosa.Model.Aggregate.Workload.workload_of_jobs`
- Certificate: `workload_of_jobs_correspondence`

## Official Rocq

```coq
workload_of_jobs :
forall {Job : JobType}, JobCost Job -> pred (Equality.sort Job) -> seq (Equality.sort Job) -> nat

workload_of_jobs is not universe polymorphic
Arguments workload_of_jobs {Job H1} P jobs%seq_scope
workload_of_jobs is transparent
Expands to: Constant prosa.model.aggregate.workload.workload_of_jobs
Declared in library prosa.model.aggregate.workload, line 20, characters 13-29
@workload_of_jobs
     : forall Job : JobType, JobCost Job -> pred (Equality.sort Job) -> seq (Equality.sort Job) -> nat
```

Body:

```coq
workload_of_jobs =
fun (Job : JobType) (H1 : JobCost Job) (P : pred (Equality.sort Job)) =>
(bigop 0)^~ (fun j : Equality.sort Job => @BigBody nat (Equality.sort Job) j addn (P j) (@job_cost Job H1 j))
     : forall {Job : JobType}, JobCost Job -> pred (Equality.sort Job) -> seq (Equality.sort Job) -> nat

Arguments workload_of_jobs {Job H1} P jobs%seq_scope
```

## Lean

```lean
@Prosa.Model.Aggregate.Workload.workload_of_jobs : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobCost Job] → (Job → Bool) → List Job → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.Workload.workload_of_jobs.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobCost Job] → (Job → Bool) → List Job → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] P jobs =>
  Prosa.Util.Sum.sumFiltered jobs P fun j => Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_Workload_workload_of_jobs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       (Job -> Bool) -> List Job -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_Workload_workload_of_jobs@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                           inst_3)
  (P : Job -> Bool) (jobs : List Job) =>
Prosa_Util_Sum_sumFiltered Job jobs P
  (fun j : Job =>
   Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_6 j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       (Job -> Bool) -> List Job -> Nat

Arguments Prosa_Model_Aggregate_Workload_workload_of_jobs Job
  inst_3
  inst_6 P%_function_scope 
  jobs
```
