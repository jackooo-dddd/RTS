# `job_deadline_from_task_deadline`

- Kind (Rocq): Instance
- Rocq: `prosa.model.task.absolute_deadline.job_deadline_from_task_deadline`
- Lean: `Prosa.Model.Task.AbsoluteDeadline.job_deadline_from_task_deadline`
- Certificate: `ad_job_deadline_from_task_deadline_certificate`

## Official Rocq

```coq
job_deadline_from_task_deadline :
forall (Job : JobType) (Task : TaskType),
TaskDeadline Task -> JobArrival Job -> JobTask Job Task -> JobDeadline Job

job_deadline_from_task_deadline is not universe polymorphic
Arguments job_deadline_from_task_deadline Job Task {H H0 H1} _
job_deadline_from_task_deadline is transparent
Expands to: Constant prosa.model.task.absolute_deadline.job_deadline_from_task_deadline
Declared in library prosa.model.task.absolute_deadline, line 8, characters 0-236
job_deadline_from_task_deadline
     : forall (Job : JobType) (Task : TaskType),
       TaskDeadline Task -> JobArrival Job -> JobTask Job Task -> JobDeadline Job
```

Body:

```coq
job_deadline_from_task_deadline =
fun (Job : JobType) (Task : TaskType) (H : TaskDeadline Task) (H0 : JobArrival Job) 
  (H1 : JobTask Job Task) (j : Equality.sort Job) =>
@job_arrival Job H0 j + @task_deadline Task H (@job_task Job Task H1 j)
     : forall (Job : JobType) (Task : TaskType),
       TaskDeadline Task -> JobArrival Job -> JobTask Job Task -> JobDeadline Job

Arguments job_deadline_from_task_deadline Job Task {H H0 H1} _
```

## Lean

```lean
Prosa.Model.Task.AbsoluteDeadline.job_deadline_from_task_deadline : (Job : Prosa.Behavior.Job.JobType) →
  (Task : Prosa.Model.Task.Concept.TaskType) →
    [inst : DecidableEq Job] →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.TaskDeadline Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] → Prosa.Behavior.Job.JobDeadline Job
@[instance_reducible] def Prosa.Model.Task.AbsoluteDeadline.job_deadline_from_task_deadline.{u_1, u_2} : (Job :
    Prosa.Behavior.Job.JobType) →
  (Task : Prosa.Model.Task.Concept.TaskType) →
    [inst : DecidableEq Job] →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.TaskDeadline Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] → Prosa.Behavior.Job.JobDeadline Job :=
fun Job Task [DecidableEq Job] [DecidableEq Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Model.Task.Concept.JobTask Job Task] =>
  {
    job_deadline := fun j =>
      Prosa.Behavior.Job.job_arrival j + Prosa.Model.Task.Concept.task_deadline (Prosa.Model.Task.Concept.job_task j) }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
     : forall (Job : Prosa_Behavior_Job_JobType) (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_4 : DecidableEq Job)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_4 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_4 Task
         inst_7 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_4
```

Body:

```coq
Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType) (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_4 : DecidableEq Job)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_TaskDeadline
                                                                              Task
                                                                              inst_7)
  (inst_13 : Prosa_Behavior_Job_JobArrival Job
                                                                              inst_4)
  (inst_16 : Prosa_Model_Task_Concept_JobTask
                                                                              Job
                                                                              inst_4
                                                                              Task
                                                                              inst_7) =>
Prosa_Behavior_Job_JobDeadline_mk Job inst_4
  (fun j : Job =>
   HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_4
        inst_13 j)
     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
        inst_7
        inst_10
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_4 Task
           inst_7
           inst_16 j)))
     : forall (Job : Prosa_Behavior_Job_JobType) (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_4 : DecidableEq Job)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_4 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_4 Task
         inst_7 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_4

Arguments Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
  inst_4
  inst_7
  inst_10
  inst_13
  inst_16
```
