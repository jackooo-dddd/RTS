# `job_cannot_be_nonpreemptive_after_completion`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.job_cannot_be_nonpreemptive_after_completion`
- Lean: `Prosa.Model.Preemption.Parameter.job_cannot_be_nonpreemptive_after_completion`
- Certificate: `job_cannot_be_nonpreemptive_after_completion_correspondence`

## Official Rocq

```coq
job_cannot_be_nonpreemptive_after_completion :
forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> bool

job_cannot_be_nonpreemptive_after_completion is not universe polymorphic
Arguments job_cannot_be_nonpreemptive_after_completion {Job H0 H1} j
job_cannot_be_nonpreemptive_after_completion is transparent
Expands to: Constant prosa.model.preemption.parameter.job_cannot_be_nonpreemptive_after_completion
Declared in library prosa.model.preemption.parameter, line 108, characters 13-57
@job_cannot_be_nonpreemptive_after_completion
     : forall Job : JobType, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> bool
```

Body:

```coq
job_cannot_be_nonpreemptive_after_completion =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (j : Equality.sort Job) =>
@job_preemptable Job H1 j (@job_cost Job H0 j)
     : forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> bool

Arguments job_cannot_be_nonpreemptive_after_completion {Job H0 H1} j
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.job_cannot_be_nonpreemptive_after_completion : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Bool
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.job_cannot_be_nonpreemptive_after_completion.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j =>
  Prosa.Model.Preemption.Parameter.job_preemptable j (Prosa.Behavior.Job.job_cost j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_job_cannot_be_nonpreemptive_after_completion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Bool
```

Body:

```coq
Prosa_Model_Preemption_Parameter_job_cannot_be_nonpreemptive_after_completion@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                             inst_3)
  (inst_9 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                             Job
                                                                             inst_3)
  (j : Job) =>
Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
  inst_3
  inst_9 j
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_6 j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Bool

Arguments Prosa_Model_Preemption_Parameter_job_cannot_be_nonpreemptive_after_completion 
  Job inst_3
  inst_6
  inst_9 j
```
