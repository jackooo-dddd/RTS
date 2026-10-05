# `end_of_execution_in_preemption_points`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.limited_preemptive.end_of_execution_in_preemption_points`
- Lean: `Prosa.Model.Preemption.LimitedPreemptive.end_of_execution_in_preemption_points`
- Certificate: `end_of_execution_in_preemption_points_correspondence`

## Official Rocq

```coq
end_of_execution_in_preemption_points :
forall {Job : JobType}, JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

end_of_execution_in_preemption_points is not universe polymorphic
Arguments end_of_execution_in_preemption_points {Job H0 H1} arr_seq
end_of_execution_in_preemption_points is transparent
Expands to: Constant prosa.model.preemption.limited_preemptive.end_of_execution_in_preemption_points
Declared in library prosa.model.preemption.limited_preemptive, line 58, characters 15-52
@end_of_execution_in_preemption_points
     : forall Job : JobType, JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop
```

Body:

```coq
end_of_execution_in_preemption_points =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptionPoints Job) (arr_seq : arrival_sequence Job) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j -> last0 (@job_preemptive_points Job H1 j) = @job_cost Job H0 j
     : forall {Job : JobType}, JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

Arguments end_of_execution_in_preemption_points {Job H0 H1} arr_seq
```

## Lean

```lean
@Prosa.Model.Preemption.LimitedPreemptive.end_of_execution_in_preemption_points : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
```

Body:

```lean
def Prosa.Model.Preemption.LimitedPreemptive.end_of_execution_in_preemption_points.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job]
    [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] arr_seq =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Util.List.last0 (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j) =
        Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_LimitedPreemptive_end_of_execution_in_preemption_points
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Preemption_LimitedPreemptive_end_of_execution_in_preemption_points@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (inst_9 : 
   Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
@eq Nat
  (Prosa_Util_List_last0
     (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
        inst_3
        inst_9 j))
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_6 j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Preemption_LimitedPreemptive_end_of_execution_in_preemption_points 
  Job inst_3
  inst_6
  inst_9 arr_seq
```
