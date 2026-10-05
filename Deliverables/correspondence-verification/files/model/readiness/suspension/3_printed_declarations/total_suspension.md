# `total_suspension`

- Kind (Rocq): Definition
- Rocq: `prosa.model.readiness.suspension.total_suspension`
- Lean: `Prosa.Model.Readiness.Suspension.total_suspension`
- Certificate: `total_suspension_correspondence`

## Official Rocq

```coq
total_suspension : forall {Job : JobType}, JobCost Job -> JobSuspension Job -> Equality.sort Job -> nat

total_suspension is not universe polymorphic
Arguments total_suspension {Job H H0} j
total_suspension is transparent
Expands to: Constant prosa.model.readiness.suspension.total_suspension
Declared in library prosa.model.readiness.suspension, line 80, characters 13-29
@total_suspension
     : forall Job : JobType, JobCost Job -> JobSuspension Job -> Equality.sort Job -> nat
```

Body:

```coq
total_suspension =
fun (Job : JobType) (H : JobCost Job) (H0 : JobSuspension Job) (j : Equality.sort Job) =>
\sum_(0 <= ρ < @job_cost Job H j) @job_suspension Job H0 j ρ
     : forall {Job : JobType}, JobCost Job -> JobSuspension Job -> Equality.sort Job -> nat

Arguments total_suspension {Job H H0} j
```

## Lean

```lean
@Prosa.Model.Readiness.Suspension.total_suspension : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Readiness.Suspension.JobSuspension Job] → Job → Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Model.Readiness.Suspension.total_suspension.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Readiness.Suspension.JobSuspension Job] → Job → Prosa.Behavior.Time.duration :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Readiness.Suspension.JobSuspension Job] j =>
  List.foldr Nat.add 0
    (List.map (Prosa.Model.Readiness.Suspension.job_suspension j) (List.range' 0 (Prosa.Behavior.Job.job_cost j - 0)))
```

## Lean, imported into Rocq

```coq
Prosa_Model_Readiness_Suspension_total_suspension
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Readiness_Suspension_JobSuspension Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Model_Readiness_Suspension_total_suspension@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                             inst_3)
  (inst_9 : Prosa_Model_Readiness_Suspension_JobSuspension
                                                                             Job
                                                                             inst_3)
  (j : Job) =>
List_foldr_inst3 Nat Prosa_Behavior_Time_duration Nat_add
  (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
  (List_map_inst3 Prosa_Behavior_Job_work Nat
     (Prosa_Model_Readiness_Suspension_JobSuspension_job_suspension Job
        inst_3
        inst_9 j)
     (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
        (HSub_hSub_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
           (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
           (Prosa_Behavior_Job_JobCost_job_cost Job
              inst_3
              inst_6 j)
           (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Readiness_Suspension_JobSuspension Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_duration

Arguments Prosa_Model_Readiness_Suspension_total_suspension Job
  inst_3
  inst_6
  inst_9 j
```
