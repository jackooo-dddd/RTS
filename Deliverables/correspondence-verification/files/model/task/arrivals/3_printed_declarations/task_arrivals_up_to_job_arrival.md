# `task_arrivals_up_to_job_arrival`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrivals.task_arrivals_up_to_job_arrival`
- Lean: `Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival`
- Certificate: `task_arrivals_up_to_job_arrival_correspondence`

## Official Rocq

```coq
task_arrivals_up_to_job_arrival :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Job -> seq (Equality.sort Job)

task_arrivals_up_to_job_arrival is not universe polymorphic
Arguments task_arrivals_up_to_job_arrival {Job Task H H0} arr_seq j
task_arrivals_up_to_job_arrival is transparent
Expands to: Constant prosa.model.task.arrivals.task_arrivals_up_to_job_arrival
Declared in library prosa.model.task.arrivals, line 81, characters 13-44
@task_arrivals_up_to_job_arrival
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       JobArrival Job -> arrival_sequence Job -> Equality.sort Job -> seq (Equality.sort Job)
```

Body:

```coq
task_arrivals_up_to_job_arrival =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
  (arr_seq : arrival_sequence Job) (j : Equality.sort Job) =>
@task_arrivals_up_to Job Task H arr_seq (@job_task Job Task H j) (@job_arrival Job H0 j)
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       JobArrival Job -> arrival_sequence Job -> Equality.sort Job -> seq (Equality.sort Job)

Arguments task_arrivals_up_to_job_arrival {Job Task H H0} arr_seq j
```

## Lean

```lean
@Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → List Job
def Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → List Job :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] arr_seq j =>
  Prosa.Model.Task.Arrivals.task_arrivals_up_to arr_seq (Prosa.Model.Task.Concept.job_task j)
    (Prosa.Behavior.Job.job_arrival j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> List Job
```

Body:

```coq
Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask Job
                                                                       inst_3
                                                                       Task
                                                                       inst_7)
  (inst_14 : Prosa_Behavior_Job_JobArrival Job
                                                                       inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (j : Job) =>
Prosa_Model_Task_Arrivals_task_arrivals_up_to Job
  inst_3 Task
  inst_7
  inst_10 arr_seq
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_3 Task
     inst_7
     inst_10 j)
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_3
     inst_14 j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> List Job

Arguments Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
  inst_3 Task
  inst_7
  inst_10
  inst_14 arr_seq j
```
