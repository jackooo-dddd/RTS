# `job_respects_task_max_np_segment`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.floating_nonpreemptive.job_respects_task_max_np_segment`
- Lean: `Prosa.Model.Task.Preemption.FloatingNonpreemptive.job_respects_task_max_np_segment`
- Certificate: `job_respects_task_max_np_segment_correspondence`

## Official Rocq

```coq
job_respects_task_max_np_segment :
forall {Task : TaskType},
TaskMaxNonpreemptiveSegment Task ->
forall {Job : JobType},
JobTask Job Task -> JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

job_respects_task_max_np_segment is not universe polymorphic
Arguments job_respects_task_max_np_segment {Task H Job H0 H1 H2} arr_seq
job_respects_task_max_np_segment is transparent
Expands to: Constant prosa.model.task.preemption.floating_nonpreemptive.job_respects_task_max_np_segment
Declared in library prosa.model.task.preemption.floating_nonpreemptive, line 38, characters 13-45
@job_respects_task_max_np_segment
     : forall Task : TaskType,
       TaskMaxNonpreemptiveSegment Task ->
       forall Job : JobType,
       JobTask Job Task -> JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop
```

Body:

```coq
job_respects_task_max_np_segment =
fun (Task : TaskType) (H : TaskMaxNonpreemptiveSegment Task) (Job : JobType) (H0 : JobTask Job Task)
  (H1 : JobCost Job) (H2 : JobPreemptionPoints Job) (arr_seq : arrival_sequence Job) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true
  (@job_max_nonpreemptive_segment Job H1 (@limited_preemptive_job_model Job H2) j <=
   @task_max_nonpreemptive_segment Task H (@job_task Job Task H0 j))
     : forall {Task : TaskType},
       TaskMaxNonpreemptiveSegment Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobCost Job -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

Arguments job_respects_task_max_np_segment {Task H Job H0 H1 H2} arr_seq
```

## Lean

```lean
@Prosa.Model.Task.Preemption.FloatingNonpreemptive.job_respects_task_max_np_segment : {Task :
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
def Prosa.Model.Task.Preemption.FloatingNonpreemptive.job_respects_task_max_np_segment.{u_1, u_2} : {Task :
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
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment j ≤
        Prosa.Model.Task.Preemption.Parameters.task_max_nonpreemptive_segment (Prosa.Model.Task.Concept.job_task j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_FloatingNonpreemptive_job_respects_task_max_np_segment
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
Prosa_Model_Task_Preemption_FloatingNonpreemptive_job_respects_task_max_np_segment@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
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
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_10 arr_seq j ->
LE_le_inst1 Nat instLENat
  (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
     inst_10
     inst_17
     (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
        inst_10
        inst_20)
     j)
  (Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment Task
     inst_3
     inst_6
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_10 Task
        inst_3
        inst_13 j))
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

Arguments Prosa_Model_Task_Preemption_FloatingNonpreemptive_job_respects_task_max_np_segment 
  Task inst_3
  inst_6 
  Job inst_10
  inst_13
  inst_17
  inst_20 
  arr_seq
```
