# `arrivals_have_positive_job_costs`

- Kind (Rocq): Definition
- Rocq: `prosa.model.job.properties.arrivals_have_positive_job_costs`
- Lean: `Prosa.Model.Job.Properties.arrivals_have_positive_job_costs`
- Certificate: `arrivals_have_positive_job_costs_correspondence`

## Official Rocq

```coq
arrivals_have_positive_job_costs : forall {Job : JobType}, JobCost Job -> arrival_sequence Job -> Prop

arrivals_have_positive_job_costs is not universe polymorphic
Arguments arrivals_have_positive_job_costs {Job H} arr_seq
arrivals_have_positive_job_costs is transparent
Expands to: Constant prosa.model.job.properties.arrivals_have_positive_job_costs
Declared in library prosa.model.job.properties, line 33, characters 13-45
@arrivals_have_positive_job_costs
     : forall Job : JobType, JobCost Job -> arrival_sequence Job -> Prop
```

Body:

```coq
arrivals_have_positive_job_costs =
fun (Job : JobType) (H : JobCost Job) (arr_seq : arrival_sequence Job) =>
forall j : Equality.sort Job, @arrives_in Job arr_seq j -> is_true (@job_cost_positive Job H j)
     : forall {Job : JobType}, JobCost Job -> arrival_sequence Job -> Prop

Arguments arrivals_have_positive_job_costs {Job H} arr_seq
```

## Lean

```lean
@Prosa.Model.Job.Properties.arrivals_have_positive_job_costs : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Model.Job.Properties.arrivals_have_positive_job_costs.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] arr_seq =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j → Prosa.Model.Job.Properties.job_cost_positive j = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Job_Properties_arrivals_have_positive_job_costs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Job_Properties_arrivals_have_positive_job_costs@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                       inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
@eq Bool
  (Prosa_Model_Job_Properties_job_cost_positive Job
     inst_3
     inst_6 j)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Job_Properties_arrivals_have_positive_job_costs Job
  inst_3
  inst_6 arr_seq
```
