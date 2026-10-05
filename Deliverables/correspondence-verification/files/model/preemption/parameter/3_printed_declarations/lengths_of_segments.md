# `lengths_of_segments`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.lengths_of_segments`
- Lean: `Prosa.Model.Preemption.Parameter.lengths_of_segments`
- Certificate: `lengths_of_segments_correspondence`

## Official Rocq

```coq
lengths_of_segments :
forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> seq nat

lengths_of_segments is not universe polymorphic
Arguments lengths_of_segments {Job H0 H1} j
lengths_of_segments is transparent
Expands to: Constant prosa.model.preemption.parameter.lengths_of_segments
Declared in library prosa.model.preemption.parameter, line 46, characters 13-32
@lengths_of_segments
     : forall Job : JobType, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> seq nat
```

Body:

```coq
lengths_of_segments =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (j : Equality.sort Job) =>
distances (@job_preemption_points Job H0 H1 j)
     : forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> seq nat

Arguments lengths_of_segments {Job H0 H1} j
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.lengths_of_segments : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → List ℕ
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.lengths_of_segments.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → List ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j =>
  Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Parameter.job_preemption_points j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_lengths_of_segments
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> List_inst1 Nat
```

Body:

```coq
Prosa_Model_Preemption_Parameter_lengths_of_segments@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                             inst_3)
  (inst_9 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                             Job
                                                                             inst_3)
  (j : Job) =>
Prosa_Util_Nondecreasing_distances
  (Prosa_Model_Preemption_Parameter_job_preemption_points Job
     inst_3
     inst_6
     inst_9 j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> List_inst1 Nat

Arguments Prosa_Model_Preemption_Parameter_lengths_of_segments Job
  inst_3
  inst_6
  inst_9 j
```
