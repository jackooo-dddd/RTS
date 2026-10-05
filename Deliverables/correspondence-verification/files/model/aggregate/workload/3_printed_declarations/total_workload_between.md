# `total_workload_between`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.workload.total_workload_between`
- Lean: `Prosa.Model.Aggregate.Workload.total_workload_between`
- Certificate: `total_workload_between_correspondence`

## Official Rocq

```coq
total_workload_between :
forall {Job : JobType}, JobCost Job -> arrival_sequence Job -> instant -> instant -> nat

total_workload_between is not universe polymorphic
Arguments total_workload_between {Job H1} arr_seq t1 t2
total_workload_between is transparent
Expands to: Constant prosa.model.aggregate.workload.total_workload_between
Declared in library prosa.model.aggregate.workload, line 46, characters 13-35
@total_workload_between
     : forall Job : JobType, JobCost Job -> arrival_sequence Job -> instant -> instant -> nat
```

Body:

```coq
total_workload_between =
fun (Job : JobType) (H1 : JobCost Job) (arr_seq : arrival_sequence Job) (t1 t2 : instant) =>
@total_workload Job H1 (@arrivals_between Job arr_seq t1 t2)
     : forall {Job : JobType}, JobCost Job -> arrival_sequence Job -> instant -> instant -> nat

Arguments total_workload_between {Job H1} arr_seq t1 t2
```

## Lean

```lean
@Prosa.Model.Aggregate.Workload.total_workload_between : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.Workload.total_workload_between.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] arr_seq t1 t2 =>
  Prosa.Model.Aggregate.Workload.total_workload (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_Workload_total_workload_between
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_Workload_total_workload_between@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                           inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Model_Aggregate_Workload_total_workload Job
  inst_3
  inst_6
  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
     inst_3 arr_seq t1 t2)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_Workload_total_workload_between Job
  inst_3
  inst_6 arr_seq t1 
  t2
```
