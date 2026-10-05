# `job_max_nonpreemptive_segment`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.job_max_nonpreemptive_segment`
- Lean: `Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment`
- Certificate: `job_max_nonpreemptive_segment_correspondence`

## Official Rocq

```coq
job_max_nonpreemptive_segment :
forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> nat

job_max_nonpreemptive_segment is not universe polymorphic
Arguments job_max_nonpreemptive_segment {Job H0 H1} j
job_max_nonpreemptive_segment is transparent
Expands to: Constant prosa.model.preemption.parameter.job_max_nonpreemptive_segment
Declared in library prosa.model.preemption.parameter, line 50, characters 13-42
@job_max_nonpreemptive_segment
     : forall Job : JobType, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> nat
```

Body:

```coq
job_max_nonpreemptive_segment =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (j : Equality.sort Job) =>
max0 (@lengths_of_segments Job H0 H1 j)
     : forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> nat

Arguments job_max_nonpreemptive_segment {Job H0 H1} j
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → ℕ
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j =>
  Prosa.Util.List.max0 (Prosa.Model.Preemption.Parameter.lengths_of_segments j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Nat
```

Body:

```coq
Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                             inst_3)
  (inst_9 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                             Job
                                                                             inst_3)
  (j : Job) =>
Prosa_Util_List_max0
  (Prosa_Model_Preemption_Parameter_lengths_of_segments Job
     inst_3
     inst_6
     inst_9 j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Nat

Arguments Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
  inst_3
  inst_6
  inst_9 j
```
