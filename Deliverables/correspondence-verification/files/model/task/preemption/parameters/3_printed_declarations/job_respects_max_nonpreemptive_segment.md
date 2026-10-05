# `job_respects_max_nonpreemptive_segment`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.parameters.job_respects_max_nonpreemptive_segment`
- Lean: `Prosa.Model.Task.Preemption.Parameters.job_respects_max_nonpreemptive_segment`
- Certificate: `job_respects_max_nonpreemptive_segment_correspondence`

## Official Rocq

```coq
job_respects_max_nonpreemptive_segment :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobCost Job -> TaskMaxNonpreemptiveSegment Task -> JobPreemptable Job -> Equality.sort Job -> bool

job_respects_max_nonpreemptive_segment is not universe polymorphic
Arguments job_respects_max_nonpreemptive_segment {Task Job H H0 H1 H2} j
job_respects_max_nonpreemptive_segment is transparent
Expands to: Constant prosa.model.task.preemption.parameters.job_respects_max_nonpreemptive_segment
Declared in library prosa.model.task.preemption.parameters, line 92, characters 13-51
@job_respects_max_nonpreemptive_segment
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobCost Job -> TaskMaxNonpreemptiveSegment Task -> JobPreemptable Job -> Equality.sort Job -> bool
```

Body:

```coq
job_respects_max_nonpreemptive_segment =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobCost Job)
  (H1 : TaskMaxNonpreemptiveSegment Task) (H2 : JobPreemptable Job) (j : Equality.sort Job) =>
@job_max_nonpreemptive_segment Job H0 H2 j <=
@task_max_nonpreemptive_segment Task H1 (@job_task Job Task H j)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobCost Job -> TaskMaxNonpreemptiveSegment Task -> JobPreemptable Job -> Equality.sort Job -> bool

Arguments job_respects_max_nonpreemptive_segment {Task Job H H0 H1 H2} j
```

## Lean

```lean
@Prosa.Model.Task.Preemption.Parameters.job_respects_max_nonpreemptive_segment : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
              [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Bool
```

Body:

```lean
def Prosa.Model.Task.Preemption.Parameters.job_respects_max_nonpreemptive_segment.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
              [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Bool :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j =>
  decide
    (Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment j ≤
      Prosa.Model.Task.Preemption.Parameters.task_max_nonpreemptive_segment (Prosa.Model.Task.Concept.job_task j))
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_job_respects_max_nonpreemptive_segment
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Job -> Bool
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_job_respects_max_nonpreemptive_segment@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (inst_14 : 
   Prosa_Behavior_Job_JobCost Job inst_7)
  (inst_17 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (inst_20 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_7)
  (j : Job) =>
Decidable_decide
  (LE_le_inst1 Nat instLENat
     (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
        inst_7
        inst_14
        inst_20 j)
     (Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment Task
        inst_3
        inst_17
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j)))
  (Nat_decLe
     (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
        inst_7
        inst_14
        inst_20 j)
     (Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment Task
        inst_3
        inst_17
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Job -> Bool

Arguments Prosa_Model_Task_Preemption_Parameters_job_respects_max_nonpreemptive_segment 
  Task inst_3 
  Job inst_7
  inst_10
  inst_14
  inst_17
  inst_20 j
```
