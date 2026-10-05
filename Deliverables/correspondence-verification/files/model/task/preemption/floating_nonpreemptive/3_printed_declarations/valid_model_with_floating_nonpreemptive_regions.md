# `valid_model_with_floating_nonpreemptive_regions`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.floating_nonpreemptive.valid_model_with_floating_nonpreemptive_regions`
- Lean: `Prosa.Model.Task.Preemption.FloatingNonpreemptive.valid_model_with_floating_nonpreemptive_regions`
- Certificate: `valid_model_with_floating_nonpreemptive_regions_correspondence`

## Official Rocq

```coq
valid_model_with_floating_nonpreemptive_regions :
forall {Task : TaskType},
TaskMaxNonpreemptiveSegment Task ->
forall {Job : JobType},
JobTask Job Task -> JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

valid_model_with_floating_nonpreemptive_regions is not universe polymorphic
Arguments valid_model_with_floating_nonpreemptive_regions {Task H Job H0 H1 H2} arr_seq
valid_model_with_floating_nonpreemptive_regions is transparent
Expands to: Constant
            prosa.model.task.preemption.floating_nonpreemptive.valid_model_with_floating_nonpreemptive_regions
Declared in library prosa.model.task.preemption.floating_nonpreemptive, line 45, characters 13-60
@valid_model_with_floating_nonpreemptive_regions
     : forall Task : TaskType,
       TaskMaxNonpreemptiveSegment Task ->
       forall Job : JobType,
       JobTask Job Task -> JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop
```

Body:

```coq
valid_model_with_floating_nonpreemptive_regions =
fun (Task : TaskType) (H : TaskMaxNonpreemptiveSegment Task) (Job : JobType) (H0 : JobTask Job Task)
  (H1 : JobCost Job) (H2 : JobPreemptionPoints Job) (arr_seq : arrival_sequence Job) =>
@valid_limited_preemptions_job_model Job H1 H2 arr_seq /\
@job_respects_task_max_np_segment Task H Job H0 H1 H2 arr_seq
     : forall {Task : TaskType},
       TaskMaxNonpreemptiveSegment Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

Arguments valid_model_with_floating_nonpreemptive_regions {Task H Job H0 H1 H2} arr_seq
```

## Lean

```lean
@Prosa.Model.Task.Preemption.FloatingNonpreemptive.valid_model_with_floating_nonpreemptive_regions : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobCost Job] →
              [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.FloatingNonpreemptive.valid_model_with_floating_nonpreemptive_regions.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobCost Job] →
              [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] {Job}
    [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobCost Job]
    [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] arr_seq =>
  Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq ∧
    Prosa.Model.Task.Preemption.FloatingNonpreemptive.job_respects_task_max_np_segment arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_FloatingNonpreemptive_valid_model_with_floating_nonpreemptive_regions
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_FloatingNonpreemptive_valid_model_with_floating_nonpreemptive_regions@{u_1 u_2
Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_10 Task
     inst_3)
  (inst_17 : 
   Prosa_Behavior_Job_JobCost Job
     inst_10)
  (inst_20 : 
   Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
     inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10) =>
And
  (Prosa_Model_Preemption_LimitedPreemptive_valid_limited_preemptions_job_model Job
     inst_10
     inst_17
     inst_20 arr_seq)
  (Prosa_Model_Task_Preemption_FloatingNonpreemptive_job_respects_task_max_np_segment Task
     inst_3
     inst_6 Job
     inst_10
     inst_13
     inst_17
     inst_20 arr_seq)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       SProp

Arguments Prosa_Model_Task_Preemption_FloatingNonpreemptive_valid_model_with_floating_nonpreemptive_regions
  Task inst_3
  inst_6 
  Job inst_10
  inst_13
  inst_17
  inst_20 
  arr_seq
```
