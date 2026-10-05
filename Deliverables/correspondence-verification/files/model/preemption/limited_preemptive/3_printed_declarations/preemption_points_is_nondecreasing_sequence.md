# `preemption_points_is_nondecreasing_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.limited_preemptive.preemption_points_is_nondecreasing_sequence`
- Lean: `Prosa.Model.Preemption.LimitedPreemptive.preemption_points_is_nondecreasing_sequence`
- Certificate: `preemption_points_is_nondecreasing_sequence_correspondence`

## Official Rocq

```coq
preemption_points_is_nondecreasing_sequence :
forall {Job : JobType}, JobPreemptionPoints Job -> arrival_sequence Job -> Prop

preemption_points_is_nondecreasing_sequence is not universe polymorphic
Arguments preemption_points_is_nondecreasing_sequence {Job H1} arr_seq
preemption_points_is_nondecreasing_sequence is transparent
Expands to: Constant prosa.model.preemption.limited_preemptive.preemption_points_is_nondecreasing_sequence
Declared in library prosa.model.preemption.limited_preemptive, line 63, characters 15-58
@preemption_points_is_nondecreasing_sequence
     : forall Job : JobType, JobPreemptionPoints Job -> arrival_sequence Job -> Prop
```

Body:

```coq
preemption_points_is_nondecreasing_sequence =
fun (Job : JobType) (H1 : JobPreemptionPoints Job) (arr_seq : arrival_sequence Job) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j -> nondecreasing_sequence (@job_preemptive_points Job H1 j)
     : forall {Job : JobType}, JobPreemptionPoints Job -> arrival_sequence Job -> Prop

Arguments preemption_points_is_nondecreasing_sequence {Job H1} arr_seq
```

## Lean

```lean
@Prosa.Model.Preemption.LimitedPreemptive.preemption_points_is_nondecreasing_sequence : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
```

Body:

```lean
def Prosa.Model.Preemption.LimitedPreemptive.preemption_points_is_nondecreasing_sequence.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] arr_seq =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Util.Nondecreasing.nondecreasing_sequence (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_LimitedPreemptive_preemption_points_is_nondecreasing_sequence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Preemption_LimitedPreemptive_preemption_points_is_nondecreasing_sequence@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
Prosa_Util_Nondecreasing_nondecreasing_sequence
  (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
     inst_3
     inst_6 j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Preemption_LimitedPreemptive_preemption_points_is_nondecreasing_sequence 
  Job inst_3
  inst_6 arr_seq
```
