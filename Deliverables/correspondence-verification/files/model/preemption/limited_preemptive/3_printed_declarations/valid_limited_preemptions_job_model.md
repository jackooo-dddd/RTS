# `valid_limited_preemptions_job_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.limited_preemptive.valid_limited_preemptions_job_model`
- Lean: `Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model`
- Certificate: `valid_limited_preemptions_job_model_correspondence`

## Official Rocq

```coq
valid_limited_preemptions_job_model :
forall {Job : JobType}, JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

valid_limited_preemptions_job_model is not universe polymorphic
Arguments valid_limited_preemptions_job_model {Job H0 H1} arr_seq
valid_limited_preemptions_job_model is transparent
Expands to: Constant prosa.model.preemption.limited_preemptive.valid_limited_preemptions_job_model
Declared in library prosa.model.preemption.limited_preemptive, line 68, characters 15-50
@valid_limited_preemptions_job_model
     : forall Job : JobType, JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop
```

Body:

```coq
valid_limited_preemptions_job_model =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptionPoints Job) (arr_seq : arrival_sequence Job) =>
@beginning_of_execution_in_preemption_points Job H1 arr_seq /\
@end_of_execution_in_preemption_points Job H0 H1 arr_seq /\
@preemption_points_is_nondecreasing_sequence Job H1 arr_seq
     : forall {Job : JobType}, JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

Arguments valid_limited_preemptions_job_model {Job H0 H1} arr_seq
```

## Lean

```lean
@Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
```

Body:

```lean
def Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job]
    [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] arr_seq =>
  Prosa.Model.Preemption.LimitedPreemptive.beginning_of_execution_in_preemption_points arr_seq ∧
    Prosa.Model.Preemption.LimitedPreemptive.end_of_execution_in_preemption_points arr_seq ∧
      Prosa.Model.Preemption.LimitedPreemptive.preemption_points_is_nondecreasing_sequence arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_LimitedPreemptive_valid_limited_preemptions_job_model
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
Prosa_Model_Preemption_LimitedPreemptive_valid_limited_preemptions_job_model@{u_1 Lean.u_1+1.0
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
And
  (Prosa_Model_Preemption_LimitedPreemptive_beginning_of_execution_in_preemption_points Job
     inst_3
     inst_9 arr_seq)
  (And
     (Prosa_Model_Preemption_LimitedPreemptive_end_of_execution_in_preemption_points Job
        inst_3
        inst_6
        inst_9 arr_seq)
     (Prosa_Model_Preemption_LimitedPreemptive_preemption_points_is_nondecreasing_sequence Job
        inst_3
        inst_9 arr_seq))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Preemption_LimitedPreemptive_valid_limited_preemptions_job_model 
  Job inst_3
  inst_6
  inst_9 arr_seq
```
