# `total_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.workload.total_workload`
- Lean: `Prosa.Model.Aggregate.Workload.total_workload`
- Certificate: `total_workload_correspondence`

## Official Rocq

```coq
total_workload : forall {Job : JobType}, JobCost Job -> seq (Equality.sort Job) -> nat

total_workload is not universe polymorphic
Arguments total_workload {Job H1} jobs%seq_scope
total_workload is transparent
Expands to: Constant prosa.model.aggregate.workload.total_workload
Declared in library prosa.model.aggregate.workload, line 43, characters 13-27
@total_workload
     : forall Job : JobType, JobCost Job -> seq (Equality.sort Job) -> nat
```

Body:

```coq
total_workload =
fun (Job : JobType) (H1 : JobCost Job) =>
     : forall {Job : JobType}, JobCost Job -> seq (Equality.sort Job) -> nat

Arguments total_workload {Job H1} jobs%seq_scope
```

## Lean

```lean
@Prosa.Model.Aggregate.Workload.total_workload : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobCost Job] → List Job → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.Workload.total_workload.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobCost Job] → List Job → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] jobs =>
  Prosa.Model.Aggregate.Workload.workload_of_jobs (fun x => true) jobs
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_Workload_total_workload
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       List Job -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_Workload_total_workload@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                           inst_3)
  (jobs : List Job) =>
Prosa_Model_Aggregate_Workload_workload_of_jobs Job
  inst_3
  inst_6 (fun _ : Job => Bool_true) jobs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       List Job -> Nat

Arguments Prosa_Model_Aggregate_Workload_total_workload Job
  inst_3
  inst_6 jobs
```
