# `job_cannot_become_nonpreemptive_before_execution`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.job_cannot_become_nonpreemptive_before_execution`
- Lean: `Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution`
- Certificate: `job_cannot_become_nonpreemptive_before_execution_correspondence`

## Official Rocq

```coq
job_cannot_become_nonpreemptive_before_execution :
forall {Job : JobType}, JobPreemptable Job -> Equality.sort Job -> bool

job_cannot_become_nonpreemptive_before_execution is not universe polymorphic
Arguments job_cannot_become_nonpreemptive_before_execution {Job H1} j
job_cannot_become_nonpreemptive_before_execution is transparent
Expands to: Constant prosa.model.preemption.parameter.job_cannot_become_nonpreemptive_before_execution
Declared in library prosa.model.preemption.parameter, line 104, characters 13-61
@job_cannot_become_nonpreemptive_before_execution
     : forall Job : JobType, JobPreemptable Job -> Equality.sort Job -> bool
```

Body:

```coq
job_cannot_become_nonpreemptive_before_execution =
fun (Job : JobType) (H1 : JobPreemptable Job) => (@job_preemptable Job H1)^~ 0
     : forall {Job : JobType}, JobPreemptable Job -> Equality.sort Job -> bool

Arguments job_cannot_become_nonpreemptive_before_execution {Job H1} j
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Bool
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j =>
  Prosa.Model.Preemption.Parameter.job_preemptable j 0
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_job_cannot_become_nonpreemptive_before_execution
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Bool
```

Body:

```coq
Prosa_Model_Preemption_Parameter_job_cannot_become_nonpreemptive_before_execution@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                            Job
                                                                            inst_3)
  (j : Job) =>
Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
  inst_3
  inst_6 j
  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Bool

Arguments Prosa_Model_Preemption_Parameter_job_cannot_become_nonpreemptive_before_execution 
  Job inst_3
  inst_6 a____at____internal__hyg0
```
