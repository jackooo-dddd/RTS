# `job_preemption_points`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.job_preemption_points`
- Lean: `Prosa.Model.Preemption.Parameter.job_preemption_points`
- Certificate: `job_preemption_points_correspondence`

## Official Rocq

```coq
job_preemption_points :
forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> seq work

job_preemption_points is not universe polymorphic
Arguments job_preemption_points {Job H0 H1} j
job_preemption_points is transparent
Expands to: Constant prosa.model.preemption.parameter.job_preemption_points
Declared in library prosa.model.preemption.parameter, line 33, characters 13-34
@job_preemption_points
     : forall Job : JobType, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> seq work
```

Body:

```coq
job_preemption_points =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (j : Equality.sort Job) =>
     : forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> seq work

Arguments job_preemption_points {Job H0 H1} j
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.job_preemption_points : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → List Prosa.Behavior.Job.work
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.job_preemption_points.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → List Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j =>
  List.filter (fun ρ => Prosa.Model.Preemption.Parameter.job_preemptable j ρ)
    (Prosa.Util.List.range 0 (Prosa.Behavior.Job.job_cost j))
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_job_preemption_points
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> List_inst1 Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Preemption_Parameter_job_preemption_points@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                            inst_3)
  (inst_9 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                            Job
                                                                            inst_3)
  (j : Job) =>
List_filter_inst1 Prosa_Behavior_Job_work
  (fun _UU03c1_ : Prosa_Behavior_Job_work =>
   Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
     inst_3
     inst_9 j _UU03c1_)
  (Prosa_Util_List_range (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
     (Prosa_Behavior_Job_JobCost_job_cost Job
        inst_3
        inst_6 j))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> List_inst1 Prosa_Behavior_Job_work

Arguments Prosa_Model_Preemption_Parameter_job_preemption_points Job
  inst_3
  inst_6
  inst_9 j
```
